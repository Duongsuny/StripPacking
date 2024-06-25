import math

from pysat.solvers import Glucose3
import fileinput
import matplotlib
import matplotlib.pyplot as plt
class Rectangle:
    def __init__(self, width, height):
        self.width = width
        self.height = height

def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

input = read_file_instance(10)
width = int(input[0])
n_rec = int(input[1])
rectangles = []

for i in input[-n_rec:]:
    rec = i.split(" ")
    rectangles.append(Rectangle(int(rec[0]), int(rec[1])))


def display_solution(strip, rectangles, pos_circuits):
    # define Matplotlib figure and axis
    fig, ax = plt.subplots()
    ax = plt.gca()
    plt.title(strip)

    if len(pos_circuits) > 0:
        for i in range(len(rectangles)):
            rect = plt.Rectangle(pos_circuits[i], rectangles[i].width, rectangles[i].height, edgecolor="#333")
            ax.add_patch(rect)

    ax.set_xlim(0, width)
    ax.set_ylim(0, strip[1] + 1)
    ax.set_xticks(range(width + 1))
    ax.set_yticks(range(strip[1] + 1))
    ax.set_xlabel('width')
    ax.set_ylabel('height')
    # display plot
    plt.show()

def OPP(strip):
    height = strip[1]
    clauses = []
    dict_count = 1
    dict = {}
    #generate p dict/order encoding
    for i in range(len(rectangles)):
        rectangle = rectangles[i]
        for e in range(0, width - rectangle.width):
            clauses.append([-dict_count, dict_count+1])
            dict["px"+ str(i + 1) + "," + str(e)] = dict_count
            if e == width - rectangle.width - 1:
                dict["px" + str(i + 1) + "," + str(e + 1)] = dict_count + 1
                dict_count = dict_count + 2
            else:
                dict_count += 1

        for f in range(0, height - rectangle.height):
            clauses.append([-dict_count, dict_count+1])
            dict["py" + str(i + 1) + "," + str(f)] = dict_count
            if f == height - rectangle.height - 1:
                dict["py" + str(i + 1) + "," + str(f + 1)] = dict_count + 1
                dict_count = dict_count + 2
            else:
                dict_count += 1

    #generate l dict
    for i in range(len(rectangles) - 1):
        for j in range(i + 1, len(rectangles)):
            dict["l" + str(i + 1) + "," + str(j + 1)] = dict_count
            dict["l" + str(j + 1) + "," + str(i + 1)] = dict_count + 1
            dict_count += 2

    #generate u dict
    for i in range(len(rectangles) - 1):
        for j in range(i + 1, len(rectangles)):
            dict["u" + str(i + 1) + "," + str(j + 1)] = dict_count
            dict["u" + str(j + 1) + "," + str(i + 1)] = dict_count + 1
            dict_count += 2

    def checkDict(key):
        nonlocal dict_count
        if key not in dict:
            dict[key] = dict_count
            dict_count += 1
        return dict[key]

    #domain-reducing constraints
    for i in range(len(rectangles)):
        for e in range(width - rectangles[i].width, width):
            clauses.append([checkDict(f"px{i + 1},{e}")])
        for f in range(height - rectangles[i].height, height):
            clauses.append([checkDict(f"py{i + 1},{f}")])


    #encoding non-overlapping constraints
    for i in range(1, len(rectangles)):
        for j in range(i + 1, len(rectangles) + 1):
            clauses.append([
                checkDict(f"l{i},{j}"),
                checkDict(f"l{j},{i}"),
                checkDict(f"u{i},{j}"),
                checkDict(f"u{j},{i}")
            ])

            for e in range(rectangles[i - 1].width):
                clauses.append([-checkDict(f"l{i},{j}"),
                                -checkDict(f"px{j},{e}")])
            for e in range(rectangles[j - 1].width):
                clauses.append([-checkDict(f"l{j},{i}"),
                                -checkDict(f"px{i},{e}")])

            for f in range(rectangles[i - 1].height):
                clauses.append([-checkDict(f"u{i},{j}"),
                                -checkDict(f"py{j},{f}")])
            for f in range(rectangles[j - 1].height):
                clauses.append([-checkDict(f"u{j},{i}"),
                                -checkDict(f"py{i},{f}")])

            for e in range(0, width - rectangles[i - 1].width):
                if f"px{j},{e + rectangles[i - 1].width}" in dict:
                    clauses.append([
                        -checkDict(f"l{i},{j}"),
                        checkDict(f"px{i},{e}"),
                        -checkDict(f"px{j},{e + rectangles[i - 1].width}"),
                    ])
                if f"px{i},{e + rectangles[j - 1].width}" in dict:
                    clauses.append([
                        -checkDict(f"l{j},{i}"),
                        checkDict(f"px{j},{e}"),
                        -checkDict(f"px{i},{e + rectangles[j - 1].width}"),
                    ])


            for f in range(0, width - rectangles[j - 1].height):
                if f"py{j},{f + rectangles[i - 1].height}" in dict:
                    clauses.append([
                        -checkDict(f"u{i},{j}"),
                        checkDict(f"py{i},{f}"),
                        -checkDict(f"py{j},{f + rectangles[i - 1].height}"),
                    ])

                if f"py{i},{f + rectangles[j - 1].height}" in dict:
                    clauses.append([
                        -checkDict(f"u{j},{i}"),
                        checkDict(f"py{j},{f}"),
                        -checkDict(f"py{i},{f + rectangles[j - 1].height}"),
                    ])


    solver = Glucose3()
    for clause in clauses:
        solver.add_clause(clause)

    if solver.solve():
        model = solver.get_model()
        print(model)
        pos = [[0 for i in range(2)] for j in range(len(rectangles))]

        result = {}
        for var in model:
            if var > 0:
                result[list(dict.keys())[list(dict.values()).index(var)]] = True
            else:
                result[list(dict.keys())[list(dict.values()).index(-var)]] = False

        for i in range(len(rectangles)):
            for e in range(width - rectangles[i].width + 1):
                if result[f"px{i + 1},{e}"] == False and result[f"px{i + 1},{e + 1}"] == True:
                    print(f"x{i + 1} = {e + 1}")
                    pos[i][0] = e + 1
                if e == 0 and result[f"px{i + 1},{e}"] == True:
                    print(f"x{i + 1} = 0")
                    pos[i][0] = 0
            for f in range(height - rectangles[i].height + 1):
                if result[f"py{i + 1},{f}"] == False and result[f"py{i + 1},{f + 1}"] == True:
                    print(f"y{i + 1} = {f + 1}")
                    pos[i][1] = f + 1
                if f == 0 and result[f"py{i + 1},{f}"] == True:
                    print(f"y{i + 1} = 0")
                    pos[i][1] = 0
        print(pos)
        display_solution((width, height), rectangles, pos)
        return(["sat", pos])
    # print(result)
    else:
        print("unsat")
        return ("unsat")


heights = [int(rectangle.height) for rectangle in rectangles]
area = math.floor(sum([int(rectangle.width * rectangle.height) for rectangle in rectangles]) / width)
upper_bound = sum(heights)
lower_bound = max(area, max(heights))

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