# multiple test
from itertools import combinations

from z3 import *
import matplotlib.pyplot as plt

import time
import fileinput


def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()


def display_solution(title, sizes_plate, n_circuits, sizes_circuits, pos_circuits):
    fig, ax = plt.subplots()
    cmap = plt.cm.get_cmap('hsv', n_circuits)
    ax = plt.gca()
    plt.title(title)
    if len(pos_circuits) > 0:
        for i in range(n_circuits):
            rect = plt.Rectangle(pos_circuits[i], *sizes_circuits[i], edgecolor="#333", facecolor=cmap(i))
            ax.add_patch(rect)
    ax.set_xlim(0, sizes_plate[0])
    ax.set_ylim(0, sizes_plate[1] + 1)
    ax.set_xticks(range(sizes_plate[0] + 1))
    ax.set_yticks(range(sizes_plate[1] + 1))
    ax.set_xlabel('width_plate')
    ax.set_ylabel('height_plate')

    plt.show()


def write_file_output(n_instance, sizes_plate, n_circuits, sizes_circuits, pos_circuits):
    filepath = "../out/out−{}.txt".format(n_instance)
    f = open(filepath, "w+")
    f.write("{} {}\n".format(*sizes_plate))
    f.write("{}\n".format(n_circuits))
    for i in range(len(pos_circuits)):
        f.write("{} {} {} {}\n".format(*sizes_circuits[i], *pos_circuits[i]))
    f.close()


def format_solution(solution):
    if not solution is None:
        X = solution["X"]
        Y = solution["Y"]
        positions = [(x, y) for x, y in zip(X, Y)]
        height = solution["HEIGHT"]
        status = solution["status"]
    else:
        positions = []
        height = 0
        status = "FAILED"
    time = solution["time"]
    backjumps = solution["backjumps"]
    return positions, height, {"time": time, "backjumps": backjumps, "status": status}


def evaluate_instance(n_instance):
    problem_instance = read_file_instance(n_instance)
    # Parameters
    width_plate = int(problem_instance[0])
    n_circuits = int(problem_instance[1])
    sizes_circuits = [[int(val) for val in i.split()] for i in problem_instance[-n_circuits:]]
    input_order, sorted_sizes_circuits = zip(*[(index, value) for index, value in
                                               sorted(enumerate(sizes_circuits), reverse=True,
                                                      key=lambda x: x[1][0] * x[1][1])])
    params_instance = dict()
    params_instance["width"] = width_plate
    params_instance["n_rects"] = n_circuits
    params_instance["width_rects"] = [sizes[0] for sizes in sorted_sizes_circuits]
    params_instance["height_rects"] = [sizes[1] for sizes in sorted_sizes_circuits]

    s = Solver()
    s.set(timeout=300000)  # in milliseconds

    start = time.time()
    positions, height_plate, stats = format_solution(solve_2DSP(s, params_instance))
    end = time.time()

    # print("Instance solved in {}".format(end - start))

    # restore the original order for the results
    sizes_plate = (width_plate, height_plate)
    original_order_positions = [x for x, _ in sorted(zip(positions, input_order), key=lambda x: x[1])]
    # display_solution("n°{} - Solved in {}".format(n_instance, end - start), sizes_plate, n_circuits, sizes_circuits,
    #                  original_order_positions)
    #write_file_output(n_instance, sizes_plate, n_circuits, sizes_circuits, original_order_positions)
    print(stats["time"], stats["backjumps"], "      ", stats["status"])


# we have variables for position for each circuit
# Them are difined with the following domain values
# D(xi) = {a ∊ N | 0 <= a <= W - wi}
# D(yi) = {a ∊ N | 0 <= a <= H - hi}

# each rectangle is represented in relation to the others: n^2 variables for each axis
# to represent the position of a rectangle i wrt j are used lr_i,j ud_i,j
# lr_i,j is true if ri is placed at the left to the rj.
# ud_i,j is true if ri is placed at the downward to the r j.

# moreover additional variables to ease the encoding:  max-min
# px_i,e is true if ri are placed at less than or equal to e.
# py_i,f is true if ri are placed at less than or equal to f .

# ph_o is true if all rectangles are packed at the downward to the height o.

def at_least_one(bool_vars):
    return Or(bool_vars)


def at_most_one(bool_vars):
    return [Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]


def exactly_one(solver, bool_vars):
    solver.add(at_most_one(bool_vars))
    solver.add(at_least_one(bool_vars))


def iff(solver, lhs, rhs):
    solver.add(And(Or(Not(lhs), rhs), Or(Not(rhs), lhs)))


def positive_range(b):
    if b < 0: return []
    return range(0, b)


def indomain(box_size, rect_size):
    return box_size - rect_size >= 0


def solve_2DSP(solver, params):
    # init the variables from the params
    # width of bounding box (= circuit plate).
    W = params["width"]
    # number of rectangles (= circuits).
    n_rects = params["n_rects"]
    # widths of rectangles
    width_rects = params["width_rects"]
    # heights of rectangles
    height_rects = params["height_rects"]
    # bounds
    min_h = max(height_rects)
    max_h = sum(height_rects)

    # Variables for 2DSP
    ph = [Bool(f"ph_{o}") for o in range(min_h, max_h)]
    sol = {}

    for o in range(max_h - min_h):
        H = o + min_h
        # Variables for 2OPP
        lr = [[Bool(f"lr^{H}_{i}_{j}") for j in range(n_rects)] for i in range(n_rects)]
        ud = [[Bool(f"ud^{H}_{i}_{j}") for j in range(n_rects)] for i in range(n_rects)]
        px = [[Bool(f"px^{H}_{i}_{e}") for e in positive_range(W - width_rects[i] + 1)] for i in range(n_rects)]
        py = [[Bool(f"py^{H}_{i}_{f}") for f in positive_range(H - height_rects[i] + 1)] for i in range(n_rects)]

        # stored for retrieve later the solution
        sol[H] = {"lr": lr, "ud": ud, "px": px, "py": py}

        # order encoding for px and py (1)
        for i in range(n_rects):
            [solver.add(Or(Not(px[i][e]), px[i][e + 1])) for e in range(len(px[i]) - 1)]
            [solver.add(Or(Not(py[i][f]), py[i][f + 1])) for f in range(len(py[i]) - 1)]

        # # Full domain restriction
        # for i in range(n_rects):
        #     for e in range(len(px[i])):
        #         if W - width_rects[i] < 0: solver.add(Not(px[i][e]))  # can we restrict to a single negation at W-1?
        #         elif e >= W - width_rects[i]: solver.add(px[i][e])  # can we restrict to a single negation at W-wi?
        #     for f in range(len(py[i])):
        #         if H - height_rects[i] < 0: solver.add(Not(py[i][f]))
        #         elif f >= H - height_rects[i]: solver.add(py[i][f])
        #
        #     solver.add(at_least_one([px[i][e] for e in range(len(px[i]))]+[Not(ph[H-min_h])]))  # necessary?
        #     solver.add(at_least_one([py[i][e] for e in range(len(py[i]))]+[Not(ph[H-min_h])]))

        # domain encoding for px and py
        for i in range(n_rects):
            if not indomain(W, width_rects[i]):
                solver.add(Not(px[i][len(px[i]) - 1]))
            else:
                solver.add(Or(ph[o], px[i][len(px[i]) - 1]))
            if not indomain(H, height_rects[i]):
                solver.add(Not(py[i][len(py[i]) - 1]))
            else:
                solver.add(Or(ph[o], py[i][len(py[i]) - 1]))

        # non overlapping constraint (2)(3)
        for i in range(n_rects):
            for j in range(n_rects):
                if i < j:
                    # domain constraint for px and py in relation to lr and ud
                    if indomain(len(px[j]) - 1, width_rects[i] - 1):
                        solver.add(Or(Not(lr[i][j]), Not(px[j][width_rects[i] - 1])))
                    else:
                        solver.add(Or(Not(lr[i][j]), Not(px[j][len(px[j]) - 1])))
                    if indomain(len(px[i]) - 1, width_rects[j] - 1):
                        solver.add(Or(Not(lr[j][i]), Not(px[i][width_rects[j] - 1])))
                    else:
                        solver.add(Or(Not(lr[j][i]), Not(px[i][len(px[i]) - 1])))
                    if indomain(len(py[j]) - 1, height_rects[i] - 1):
                        solver.add(Or(Not(ud[i][j]), Not(py[j][height_rects[i] - 1])))
                    else:
                        solver.add(Or(Not(ud[i][j]), Not(py[j][len(py[j]) - 1])))
                    if indomain(len(py[i]) - 1, height_rects[j] - 1):
                        solver.add(Or(Not(ud[j][i]), Not(py[i][height_rects[j] - 1])))
                    else:
                        solver.add(Or(Not(ud[j][i]), Not(py[i][len(py[i]) - 1])))

                    # symmetries for the problem
                    # if (width_rects[i], height_rects[i]) == (width_rects[j], height_rects[j]):
                    #     # SR
                    #     solver.add(Or(lr[i][j], ud[i][j], ud[j][i]))
                    #     solver.add(Or(Not(ud[i][j]), lr[j][i]))
                    #
                    #     [solver.add(Or(ph[o], Not(lr[i][j]), px[i][e], Not(px[j][e + width_rects[i]]))) for e in positive_range(W - width_rects[i]) if indomain(len(px[j]) - 1, e + width_rects[i])]
                    #
                    #     [solver.add(Or(ph[o], Not(ud[i][j]), py[i][f], Not(py[j][f + height_rects[i]]))) for f in positive_range(H - height_rects[j]) if indomain(len(py[j]) - 1, f + height_rects[i])]
                    #
                    #     [solver.add(Or(ph[o], Not(ud[j][i]), py[j][f], Not(py[i][f + height_rects[j]]))) for f in positive_range(H - height_rects[j]) if indomain(len(py[i]) - 1, f + height_rects[j])]
                    # elif width_rects[i]+width_rects[j]>W:
                    #     # LRH (only h, this technique in the vertical direction doesn't perform good)
                    #     solver.add(Or(ud[i][j], ud[j][i]))
                    #
                    #     [solver.add(Or(ph[o], Not(ud[i][j]), py[i][f], Not(py[j][f + height_rects[i]]))) for f in positive_range(H - height_rects[j]) if indomain(len(py[j]) - 1, f + height_rects[i])]
                    #
                    #     [solver.add(Or(ph[o], Not(ud[j][i]), py[j][f], Not(py[i][f + height_rects[j]]))) for f in positive_range(H - height_rects[j]) if indomain(len(py[i]) - 1, f + height_rects[j])]
                    #
                    # elif width_rects[i]>(W-width_rects[j])/2:
                    #     # LS domain reduction
                    #     solver.add(Or(lr[j][i], ud[i][j], ud[j][i]))
                    #
                    #     [solver.add(Or(ph[o], Not(lr[j][i]), px[j][e], Not(px[i][e + width_rects[j]]))) for e in positive_range(W - width_rects[i]) if indomain(len(px[i]) - 1, e + width_rects[j])]
                    #
                    #     [solver.add(Or(ph[o], Not(ud[i][j]), py[i][f], Not(py[j][f + height_rects[i]]))) for f in positive_range(H - height_rects[j]) if indomain(len(py[j]) - 1, f + height_rects[i])]
                    #
                    #     [solver.add(Or(ph[o], Not(ud[j][i]), py[j][f], Not(py[i][f + height_rects[j]]))) for f in  positive_range(H - height_rects[j]) if indomain(len(py[i]) - 1, f + height_rects[j])]
                    # else:
                    # regular case
                    solver.add(Or(lr[i][j], lr[j][i], ud[i][j], ud[j][i]))

                    [solver.add(Or(ph[o], Not(lr[i][j]), px[i][e], Not(px[j][e + width_rects[i]]))) for e in
                     positive_range(W - width_rects[i]) if indomain(len(px[j]) - 1, e + width_rects[i])]

                    [solver.add(Or(ph[o], Not(lr[j][i]), px[j][e], Not(px[i][e + width_rects[j]]))) for e in
                     positive_range(W - width_rects[i]) if indomain(len(px[i]) - 1, e + width_rects[j])]

                    [solver.add(Or(ph[o], Not(ud[i][j]), py[i][f], Not(py[j][f + height_rects[i]]))) for f in
                     positive_range(H - height_rects[j]) if indomain(len(py[j]) - 1, f + height_rects[i])]

                    [solver.add(Or(ph[o], Not(ud[j][i]), py[j][f], Not(py[i][f + height_rects[j]]))) for f in
                     positive_range(H - height_rects[j]) if indomain(len(py[i]) - 1, f + height_rects[j])]
        # (4)
        # constraint for 2DSP variables
        if H + 1 >= max_h: solver.add(ph[o])
        exactly_one(solver, ([Not(ph[o]) for o in range(len(ph))]))

    for H, vars in sol.items():
        lr, ud, px, py = vars.values()
        o = H - min_h
        if H + 1 < max_h:
            # order encoding for 2OPP which are valid solutions and therefore respect the validity check on py variables
            solver.add(Or([Not(py[i][len(py[i]) - 1]) for i in range(n_rects)] + [
                And([sol[H + 1]["py"][i][len(sol[H + 1]["py"][i]) - 1] for i in range(n_rects)] + [ph[o + 1]])]))
            # constraint to encode the first solvable 2OPP as the valid solution
            solver.add(Or([And([py[i][len(py[i]) - 1] for i in range(n_rects)])] + [
                Not(sol[H + 1]["py"][i][len(sol[H + 1]["py"][i]) - 1]) for i in range(n_rects)] + [Not(ph[o + 1])]))
    X = []
    Y = []
    if solver.check() == sat:
        model = solver.model()
        for o in range(max_h - min_h):
            if str(model.evaluate(ph[o])) == 'False':
                print(f"Found best height at {o + min_h}");
                break

        H = o + min_h
        lr, ud, px, py = sol[H].values()
        if H != max_h - 1:
            status = "SOLVED"
            for i in range(n_rects):
                for e in range(len(px[i])):
                    if str(model.evaluate(px[i][e])) == 'True': X.append(e); break
                for f in range(len(py[i])):
                    if str(model.evaluate(py[i][f])) == 'True': Y.append(f); break
        else:
            status = "NOT SOLVED"
    elif solver.reason_unknown() == "timeout":
        print("Solver timeout")
        status = "TIMEOUT"
    else:
        print("Failed to solve at height {}".format(H))
        status = "FAILED"
    return {"X": X, "Y": Y, "HEIGHT": H, "status": status,
            "backjumps": solver.statistics().sat_backjumps,
            "time": solver.statistics().time}


if __name__ == '__main__':
    N_INSTANCE = 2

    # for i in range(1, 41):
    #     evaluate_instance(i)

    evaluate_instance(N_INSTANCE)