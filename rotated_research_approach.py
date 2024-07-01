import math

from pysat.formula import CNF
from pysat.solvers import Solver

import fileinput
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
# Define the rectangles and the strip
import timeit

start = timeit.default_timer()


# Initialize the CNF formula

# read file
def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()


def display_solution(strip, rectangles, pos_circuits, rotation):
    # define Matplotlib figure and axis
    fig, ax = plt.subplots()
    ax = plt.gca()
    plt.title(strip)

    if len(pos_circuits) > 0:
        for i in range(len(rectangles)):
            rect = plt.Rectangle(pos_circuits[i],
                                 rectangles[i][0] if not rotation[i] else rectangles[i][1],
                                 rectangles[i][1] if not rotation[i] else rectangles[i][0],
                                 edgecolor="#333")
            ax.add_patch(rect)

    ax.set_xlim(0, strip[0])
    ax.set_ylim(0, strip[1] + 1)
    ax.set_xticks(range(strip[0] + 1))
    ax.set_yticks(range(strip[1] + 1))
    ax.set_xlabel('width')
    ax.set_ylabel('height')
    # display plot
    plt.show()


# read file input
input = read_file_instance(10)
width = int(input[0])
n_rec = int(input[1])
rectangles = [[int(val) for val in i.split()] for i in input[-n_rec:]]


# print(rectangles)


def positive_range(end):
    if (end < 0):
        return []
    return range(end)


def OPP(strip):
    # Define the variables
    height = int(strip[1])
    cnf = CNF()
    variables = {}
    counter = 1
    max_height = max([int(rectangle[1]) for rectangle in rectangles])
    max_width = max([int(rectangle[0]) for rectangle in rectangles])

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
        # cnf.append([variables[f"r{i + 1}"]])
        counter += 1

    # Add the 2-literal axiom clauses
    for i in range(len(rectangles)):
        for e in range(width - 1):  # -1 because we're using e+1 in the clause
            cnf.append([-variables[f"px{i + 1},{e}"],
                        variables[f"px{i + 1},{e + 1}"]])
        for f in range(height - 1):  # -1 because we're using f+1 in the clause
            cnf.append([-variables[f"py{i + 1},{f}"],
                        variables[f"py{i + 1},{f + 1}"]])

    # Add the 3-literal non-overlapping constraints

    def non_overlapping(i_rotated, j_rotated, i, j, h1, h2, v1, v2):
        if not i_rotated:
            i_width = rectangles[i][0]
            i_height = rectangles[i][1]
            i_rotation = variables[f"r{i + 1}"]
        else:
            i_width = rectangles[i][1]
            i_height = rectangles[i][0]
            i_rotation = -variables[f"r{i + 1}"]

        if not j_rotated:
            j_width = rectangles[j][0]
            j_height = rectangles[j][1]
            j_rotation = variables[f"r{j + 1}"]
        else:
            j_width = rectangles[j][1]
            j_height = rectangles[j][0]
            j_rotation = -variables[f"r{j + 1}"]

        four_literal = [i_rotation, j_rotation]
        if h1: four_literal.append(variables[f"lr{i + 1},{j + 1}"])
        if h2: four_literal.append(variables[f"lr{j + 1},{i + 1}"])
        if v1: four_literal.append(variables[f"ud{i + 1},{j + 1}"])
        if v2: four_literal.append(variables[f"ud{j + 1},{i + 1}"])
        cnf.append(four_literal)

        # ¬lri, j ∨ ¬pxj, e
        if h1 and not (i_rotated is False and j_rotated is True):
            for e in range(min(width, i_width)):
                cnf.append([i_rotation,
                            -variables[f"lr{i + 1},{j + 1}"],
                            -variables[f"px{j + 1},{e}"]])
        # ¬lrj,i ∨ ¬pxi,e
        if h2 and not (j_rotated is False and i_rotated is True):
            for e in range(min(width, j_width)):
                cnf.append([j_rotation,
                            -variables[f"lr{j + 1},{i + 1}"],
                            -variables[f"px{i + 1},{e}"]])
        # ¬udi,j ∨ ¬pyj,f
        if v1 and not (i_rotated is False and j_rotated is True):
            for f in range(min(height, i_height)):
                cnf.append([i_rotation,
                            -variables[f"ud{i + 1},{j + 1}"],
                            -variables[f"py{j + 1},{f}"]])
        # ¬udj, i ∨ ¬pyi, f,
        if v2 and not (j_rotated is False and i_rotated is True):
            for f in range(min(height, j_height)):
                cnf.append([j_rotation,
                            -variables[f"ud{j + 1},{i + 1}"],
                            -variables[f"py{i + 1},{f}"]])

        if not (i_rotated is False and j_rotated is True):
            for e in positive_range(width - i_width):
                # ¬lri,j ∨ ¬pxj,e+wi ∨ pxi,e
                if h1:
                    cnf.append([i_rotation,
                                -variables[f"lr{i + 1},{j + 1}"],
                                variables[f"px{i + 1},{e}"],
                                -variables[f"px{j + 1},{e + i_width}"]])

        if not (j_rotated is False and i_rotated is True):
            for e in positive_range(width - j_width):
                # ¬lrj,i ∨ ¬pxi,e+wj ∨ pxj,e
                if h2:
                    cnf.append([j_rotation,
                                -variables[f"lr{j + 1},{i + 1}"],
                                variables[f"px{j + 1},{e}"],
                                -variables[f"px{i + 1},{e + j_width}"]])

        if not (i_rotated is False and j_rotated is True):
            for f in positive_range(height - i_height):
                # udi,j ∨ ¬pyj,f+hi ∨ pxi,e
                if v1:
                    cnf.append([i_rotation,
                                -variables[f"ud{i + 1},{j + 1}"],
                                variables[f"py{i + 1},{f}"],
                                -variables[f"py{j + 1},{f + i_height}"]])
        if not (j_rotated is False and i_rotated is True):
            for f in positive_range(height - j_height):
                # ¬udj,i ∨ ¬pyi,f+hj ∨ pxj,f
                if v2:
                    cnf.append([j_rotation,
                                -variables[f"ud{j + 1},{i + 1}"],
                                variables[f"py{j + 1},{f}"],
                                -variables[f"py{i + 1},{f + j_height}"]])

    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
             #Large-rectangles horizontal
             if rectangles[i][0] + rectangles[j][0] > width:
                 non_overlapping(False, False, i, j, False, False, True, True)
             else:
                 non_overlapping(False,  False, i, j, True, True, True, True)
            # # #  #Large-rectangles vertical

            # #
            # #  #Same-sized rectangles
            # #  elif rectangles[i] == rectangles[j]:
            # #      non_overlapping(False, i, j, True, False, True, True)
            # #  #
            # #  #largest width rectangle
            # #  elif rectangles[i][0] == max_width and rectangles[j][0] > (width - max_width) / 2:
            # #      non_overlapping(False, i, j, False, True, True, True)
            # #  #
            # #  #largest height rectangle
            # #  elif rectangles[i][1] == max_height and rectangles[j][1] > (height - max_height) / 2:
            # #      non_overlapping(False, i, j, True, True, False, True)
            # # # #normal rectangles

             # if rectangles[i][0] + rectangles[j][1] > width:
             #    non_overlapping(True, False, i, j, False, False, True, True)
             # elif rectangles[i][1] + rectangles[j][0] > width:
             #     non_overlapping(False, True, i, j, False, False, True, True)
             # elif rectangles[i][0] + rectangles[j][1] > height:
             #    non_overlapping(False, True, i, j, True, True, False, False)
             # elif rectangles[i][1] + rectangles[j][0] > height:
             #     non_overlapping(True, False, i, j, True, True, False, False)
             # else:
                 non_overlapping(True, True, i, j, True, True, True, True)

            # Rotation
            # Large-rectangles horizontal
            # if rectangles[i][1] + rectangles[j][0] > width or rectangles[i][0] + rectangles[j][1] > width:
            #     non_overlapping(True, i, j, False, False, True, True)
            #     #  #Large-rectangles vertical
            # elif rectangles[i][1] + rectangles[j][0] > height or rectangles[i][0] + rectangles[j][1] > height:
            #     non_overlapping(True, i, j, True, True, False, False)
            # else:
            #     non_overlapping(True, i, j, True, True, True, True)

    # Domain encoding

    for i in range(len(rectangles)):
        if rectangles[i][0] > width:
            cnf.append([variables[f"r{i + 1}"]])
        else:
            for e in range(width - rectangles[i][0], width):
                cnf.append([variables[f"r{i + 1}"],
                            variables[f"px{i + 1},{e}"]])
        if rectangles[i][1] > height:
            cnf.append([variables[f"r{i + 1}"]])
        else:
            for f in range(height - rectangles[i][1], height):
                cnf.append([variables[f"r{i + 1}"],
                            variables[f"py{i + 1},{f}"]])

        # Rotated
        if rectangles[i][1] > width:
            cnf.append([-variables[f"r{i + 1}"]])
        else:
            for e in range(width - rectangles[i][1], width):
                cnf.append([-variables[f"r{i + 1}"],
                            variables[f"px{i + 1},{e}"]])
        if rectangles[i][0] > height:
            cnf.append([-variables[f"r{i + 1}"]])
        else:
            for f in range(height - rectangles[i][0], height):
                cnf.append([-variables[f"r{i + 1}"],
                            variables[f"py{i + 1},{f}"]])

    with Solver(name="mc") as solver:
        solver.append_formula(cnf)

        if solver.solve():
            pos = [[0 for i in range(2)] for j in range(len(rectangles))]
            rotation = []
            model = solver.get_model()
            print("SAT")
            result = {}
            for var in model:
                if var > 0:
                    result[list(variables.keys())[list(variables.values()).index(var)]] = True
                else:
                    result[list(variables.keys())[list(variables.values()).index(-var)]] = False
            # print(result)

            for i in range(len(rectangles)):
                rotation.append(result[f"r{i + 1}"])
                for e in range(width - 1):
                    if result[f"px{i + 1},{e}"] == False and result[f"px{i + 1},{e + 1}"] == True:
                        print(f"x{i + 1} = {e + 1}")
                        pos[i][0] = e + 1
                    if e == 0 and result[f"px{i + 1},{e}"] == True:
                        print(f"x{i + 1} = 0")
                        pos[i][0] = 0
                for f in range(height - 1):
                    if result[f"py{i + 1},{f}"] == False and result[f"py{i + 1},{f + 1}"] == True:
                        print(f"y{i + 1} = {f + 1}")
                        pos[i][1] = f + 1
                    if f == 0 and result[f"py{i + 1},{f}"] == True:
                        print(f"y{i + 1} = 0")
                        pos[i][1] = 0
            print(pos, rotation)
            display_solution(strip, rectangles, pos, rotation)
            return (["sat", pos])

        else:
            print("unsat")
            return ("unsat")


# solving 2SPP
heights = [int(rectangle[1]) for rectangle in rectangles]
area = math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width)
upper_bound = sum(heights)
lower_bound = area
optimal_height = 0
optimal_pos = []


def SPP(lower, upper):
    if lower <= upper:
        mid = (lower + upper) // 2
        print(lower, upper, mid)
        OPP_result = OPP((width, mid))
        if OPP_result[0] == "sat":
            global optimal_height, optimal_pos
            optimal_height = mid
            optimal_pos = OPP_result[1]

            if lower + 1 == upper:
                return -1
            else:
                SPP(lower, mid)
        else:
            if lower + 1 == upper:
                return -1
            else:
                SPP(mid, upper)
    else:
        return -1


SPP(lower_bound, upper_bound)
# print(optimal_height)
# display_solution((width, optimal_height), rectangles, optimal_pos)
# OPP((14, 14))

stop = timeit.default_timer()
print('Time: ', stop - start)
