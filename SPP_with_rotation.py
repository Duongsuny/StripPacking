import math
from pysat.formula import CNF
from pysat.solvers import Solver
import fileinput
import matplotlib.pyplot as plt
import timeit

start = timeit.default_timer()  # start clock

# read file
def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

def display_solution(strip, rectangles, pos_circuits, rotations):
    fig, ax = plt.subplots()
    plt.title(f"Strip Packing Solution (Width: {strip[0]}, Height: {strip[1]})")

    if len(pos_circuits) > 0:
        for i in range(len(rectangles)):
            w = rectangles[i][1] if rotations[i] else rectangles[i][0]
            h = rectangles[i][0] if rotations[i] else rectangles[i][1]
            rect = plt.Rectangle(pos_circuits[i], w, h, 
                               edgecolor="#333", facecolor="lightblue", alpha=0.6)
            ax.add_patch(rect)
            rx, ry = pos_circuits[i]
            cx, cy = rx + w/2, ry + h/2
            ax.annotate(str(i), (cx, cy), color='black', ha='center', va='center')

    ax.set_xlim(0, strip[0])
    ax.set_ylim(0, strip[1] + 1)
    ax.set_xticks(range(strip[0] + 1))
    ax.set_yticks(range(int(strip[1]) + 2))
    ax.set_xlabel('Width')
    ax.set_ylabel('Height')
    ax.grid(True, linestyle='--', alpha=0.7)
    plt.show()

# read file input
input_data = read_file_instance(10)# instance 0 - 40
width = int(input_data[0])
n_rec = int(input_data[1])
rectangles = [[int(val) for val in i.split()] for i in input_data[-n_rec:]]
# Sort rectangles by area (width × height) in descending order
#rectangles.sort(key=lambda x: x[0] * x[1])

def positive_range(end):
    if end < 0:
        return []
    return range(end)

def OPP(strip):
    height = int(strip[1])
    cnf = CNF()
    variables = {}
    counter = 1

    for i in range(len(rectangles)):
        for j in range(len(rectangles)):
            if i != j:
                variables[f"lr{i + 1},{j + 1}"] = counter  # lri,rj
                counter += 1
                variables[f"ud{i + 1},{j + 1}"] = counter  # uri,rj
                counter += 1
        for e in range(width):
            variables[f"px{i + 1},{e}"] = counter  # pxi,e
            counter += 1
        for f in range(height):
            variables[f"py{i + 1},{f}"] = counter  # pyi,f
            counter += 1

    # Rotated variables
    for i in range(len(rectangles)):
        variables[f"r{i + 1}"] = counter
        counter += 1

    # Add the 2-literal axiom clauses
    for i in range(len(rectangles)):
        for e in range(width - 1):  # -1 because we're using e+1 in the clause
            cnf.append([-variables[f"px{i + 1},{e}"],
                        variables[f"px{i + 1},{e + 1}"]])
        for f in range(height - 1):  # -1 because we're using f+1 in the clause
            cnf.append([-variables[f"py{i + 1},{f}"],
                        variables[f"py{i + 1},{f + 1}"]])

    # Add non-overlapping constraints
    def non_overlapping(rotated, i, j, h1, h2, v1, v2):
        # Get dimensions based on rotation
        if not rotated:
            i_width = rectangles[i][0]
            i_height = rectangles[i][1]
            j_width = rectangles[j][0]
            j_height = rectangles[j][1]
            i_rotation = variables[f"r{i + 1}"]
            j_rotation = variables[f"r{j + 1}"]
        else:
            i_width = rectangles[i][1]
            i_height = rectangles[i][0]
            j_width = rectangles[j][1]
            j_height = rectangles[j][0]
            i_rotation = -variables[f"r{i + 1}"]
            j_rotation = -variables[f"r{j + 1}"]

        # lri,j v lrj,i v udi,j v udj,i
        four_literal = []
        if h1: four_literal.append(variables[f"lr{i + 1},{j + 1}"])
        if h2: four_literal.append(variables[f"lr{j + 1},{i + 1}"])
        if v1: four_literal.append(variables[f"ud{i + 1},{j + 1}"])
        if v2: four_literal.append(variables[f"ud{j + 1},{i + 1}"])

        cnf.append(four_literal + [i_rotation])
        cnf.append(four_literal + [j_rotation])

        # Optimize range checks
        max_width = min(width, max(i_width, j_width))
        max_height = min(height, max(i_height, j_height))

        # Add constraints only if they're necessary
        if h1:
            for e in range(min(width, i_width)):
                cnf.append([i_rotation, -variables[f"lr{i + 1},{j + 1}"], -variables[f"px{j + 1},{e}"]])
        
        if h2:
            for e in range(min(width, j_width)):
                cnf.append([j_rotation,
                            -variables[f"lr{j + 1},{i + 1}"],
                            -variables[f"px{i + 1},{e}"]])
        # ¬udi,j ∨ ¬pyj,f
        if v1:
            for f in range(min(height, i_height)):
                cnf.append([i_rotation,
                            -variables[f"ud{i + 1},{j + 1}"],
                            -variables[f"py{j + 1},{f}"]])
        # ¬udj,i ∨ ¬pyi,f
        if v2:
            for f in range(min(height, j_height)):
                cnf.append([j_rotation,
                            -variables[f"ud{j + 1},{i + 1}"],
                            -variables[f"py{i + 1},{f}"]])

        for e in positive_range(width - i_width):
            # ¬lri,j ∨ ¬pxj,e+wi ∨ pxi,e
            if h1:
                cnf.append([i_rotation,
                            -variables[f"lr{i + 1},{j + 1}"],
                            variables[f"px{i + 1},{e}"],
                            -variables[f"px{j + 1},{e + i_width}"]])

        for e in positive_range(width - j_width):
            # ¬lrj,i ∨ ¬pxi,e+wj ∨ pxj,e
            if h2:
                cnf.append([j_rotation,
                            -variables[f"lr{j + 1},{i + 1}"],
                            variables[f"px{j + 1},{e}"],
                            -variables[f"px{i + 1},{e + j_width}"]])

        for f in positive_range(height - i_height):
            # ¬udi,j ∨ ¬pyj,f+hi ∨ pxi,e
            if v1:
                cnf.append([i_rotation,
                            -variables[f"ud{i + 1},{j + 1}"],
                            variables[f"py{i + 1},{f}"],
                            -variables[f"py{j + 1},{f + i_height}"]])
        for f in positive_range(height - j_height):
            # ¬udj,i ∨ ¬pyi,f+hj ∨ pxj,f
            if v2:
                cnf.append([j_rotation,
                            -variables[f"ud{j + 1},{i + 1}"],
                            variables[f"py{j + 1},{f}"],
                            -variables[f"py{i + 1},{f + j_height}"]])

    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            # Large-rectangles horizontal
            if min(rectangles[i][0], rectangles[i][1]) + min(rectangles[j][0], rectangles[j][1]) > width:
                non_overlapping(False, i, j, False, False, True, True)
                non_overlapping(True, i, j, False, False, True, True)
            # Large rectangles vertical
            elif min(rectangles[i][0], rectangles[i][1]) + min(rectangles[j][0], rectangles[j][1]) > height:
                non_overlapping(False, i, j, True, True, False, False)
                non_overlapping(True, i, j, True, True, False, False)
            # Same rectangle and is a square

            # Normal rectangles
            else:
                non_overlapping(False, i, j, True, True, True, True)
                non_overlapping(True, i, j, True, True, True, True)

    # Domain encoding to ensure every rectangle stays inside strip's boundary
    for i in range(len(rectangles)):
        if rectangles[i][0] > width:
            cnf.append([variables[f"r{i + 1}"]])  # Fixed: wrapped in list
        else:
            for e in range(width - rectangles[i][0], width):
                cnf.append([variables[f"r{i + 1}"],
                            variables[f"px{i + 1},{e}"]])
        if rectangles[i][1] > height:
            cnf.append([variables[f"r{i + 1}"]])  # Fixed: wrapped in list
        else:
            for f in range(height - rectangles[i][1], height):
                cnf.append([variables[f"r{i + 1}"],
                            variables[f"py{i + 1},{f}"]])

        # Rotated
        if rectangles[i][1] > width:
            cnf.append([-variables[f"r{i + 1}"]])  # Fixed: wrapped in list
        else:
            for e in range(width - rectangles[i][1], width):
                cnf.append([-variables[f"r{i + 1}"],
                            variables[f"px{i + 1},{e}"]])
        if rectangles[i][0] > height:
            cnf.append([-variables[f"r{i + 1}"]])  # Fixed: wrapped in list
        else:
            for f in range(height - rectangles[i][0], height):
                cnf.append([-variables[f"r{i + 1}"],
                            variables[f"py{i + 1},{f}"]])

    with Solver(name="mc") as solver:  # Add all cnf to solver
        solver.append_formula(cnf)

        if solver.solve():
            pos = [[0 for _ in range(2)] for _ in range(len(rectangles))]
            rotation = []
            model = solver.get_model()
            result = {}
            for var in model:
                if var > 0:
                    result[list(variables.keys())[list(variables.values()).index(var)]] = True
                else:
                    result[list(variables.keys())[list(variables.values()).index(-var)]] = False

            for i in range(len(rectangles)):
                rotation.append(result[f"r{i + 1}"])
                for e in range(width - 1):
                    if result[f"px{i + 1},{e}"] == False and result[f"px{i + 1},{e + 1}"] == True:
                        pos[i][0] = e + 1
                    if e == 0 and result[f"px{i + 1},{e}"] == True:
                        pos[i][0] = 0
                for f in range(height - 1):
                    if result[f"py{i + 1},{f}"] == False and result[f"py{i + 1},{f + 1}"] == True:
                        pos[i][1] = f + 1
                    if f == 0 and result[f"py{i + 1},{f}"] == True:
                        pos[i][1] = 0
            return ["sat", pos, rotation]
        else:
            return "unsat"

# Solving 2SPP
heights = [int(rectangle[1]) for rectangle in rectangles]
widths = [int(rectangle[0]) for rectangle in rectangles]
upper_bound = sum(heights)
lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(max(heights), max(widths)))

optimal_height = 0
optimal_pos = []
optimal_rot = []

def SPP(lower, upper):
    if lower <= upper:
        mid = (lower + upper) // 2
        OPP_result = OPP((width, mid))
        if OPP_result == "unsat":
            if lower + 1 == upper:
                return -1
            else:
                return SPP(mid, upper)
        else:
            global optimal_height, optimal_pos, optimal_rot
            optimal_height = mid
            optimal_pos = OPP_result[1]
            optimal_rot = OPP_result[2]
            if lower + 1 == upper:
                return -1
            else:
                return SPP(lower, mid)
    else:
        return -1

SPP(lower_bound, upper_bound)
stop = timeit.default_timer()
print(f"Optimal strip height: {optimal_height}")
print(f"Solve time: {stop - start:.2f} seconds")
print(f"Lower bound: {lower_bound}")
print(f"Upper bound: {upper_bound}")
print("Rectangle positions (x, y) and rotation status:")
for i, (x_pos, y_pos) in enumerate(optimal_pos):
    rot_status = "Rotated" if optimal_rot[i] else "Not Rotated"
    effective_w = rectangles[i][1] if optimal_rot[i] else rectangles[i][0]
    effective_h = rectangles[i][0] if optimal_rot[i] else rectangles[i][1]
    print(f"Rectangle {i}: ({x_pos}, {y_pos}) "
          f"width={effective_w}, height={effective_h}, {rot_status}")

strip = [width, optimal_height]
display_solution(strip, rectangles, optimal_pos, optimal_rot)