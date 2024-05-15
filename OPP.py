from pysat.formula import CNF
from pysat.solvers import Solver

# Define the rectangles and the strip
rectangles = [(1, 2), (1, 2), (2, 1), (1, 1)]  # (width, height)
strip = (4, 3)  # (width, height)

# Initialize the CNF formula
cnf = CNF()


def positive_range(end):
    if (end < 0):
        return []
    return range(end)


# Define the variables
variables = {}
counter = 1
for i in range(len(rectangles)):
    for j in range(len(rectangles)):
        variables[f"lr{i + 1},{j + 1}"] = counter  # lri,rj
        counter += 1
        variables[f"ud{i + 1},{j + 1}"] = counter  # uri,rj
        counter += 1
    for e in positive_range(strip[0] - rectangles[i][0] + 2):
        variables[f"px{i + 1},{e}"] = counter  # pxi,e
        counter += 1
    for f in positive_range(strip[1] - rectangles[i][1] + 2):
        variables[f"py{i + 1},{f}"] = counter  # pyi,f
        counter += 1

# print the variables
print(variables)

# Add the 2-literal axiom clauses
for i in range(len(rectangles)):
    for e in range(strip[0] - rectangles[i][0] + 1):  # -1 because we're using e+1 in the clause
        cnf.append([-variables[f"px{i + 1},{e}"], variables[f"px{i + 1},{e + 1}"]])
    for f in range(strip[1] - rectangles[i][1] + 1):  # -1 because we're using f+1 in the clause
        cnf.append([-variables[f"py{i + 1},{f}"], variables[f"py{i + 1},{f + 1}"]])

# Add the 4-literal axiom clauses
for i in range(len(rectangles)):
    for j in range(i + 1, len(rectangles)):
        cnf.append([variables[f"lr{i + 1},{j + 1}"], variables[f"lr{j + 1},{i + 1}"], variables[f"ud{i + 1},{j + 1}"],
                    variables[f"ud{j + 1},{i + 1}"]])

# Add the 3-literal non-overlapping constraints
for i in range(len(rectangles)):
    for j in range(i + 1, len(rectangles)):
        for e in positive_range(strip[0] - rectangles[i][0]):
            cnf.append([-variables[f"lr{i + 1},{j + 1}"], -variables.get(f"px{j + 1},{rectangles[i][0] - 1}", 0)])
            cnf.append([-variables[f"lr{i + 1},{j + 1}"],
                        variables[f"px{i + 1},{strip[0] - rectangles[i][0] - rectangles[j][0]}"]])

            cnf.append([-variables[f"lr{i + 1},{j + 1}"], variables[f"px{i + 1},{e}"],
                        -variables.get(f"px{j + 1},{e + rectangles[i][0]}", 0)])
            cnf.append([-variables[f"lr{j + 1},{i + 1}"], variables.get(f"px{j + 1},{e}", 0),
                        -variables.get(f"px{i + 1},{e + rectangles[j][0]}", 0)])
        for f in positive_range(strip[1] - rectangles[i][1]):
            cnf.append([-variables[f"ud{i + 1},{j + 1}"], -variables.get(f"py{j + 1},{rectangles[i][1] - 1}", 0)])
            cnf.append([-variables[f"ud{i + 1},{j + 1}"],
                        variables[f"py{i + 1},{strip[1] - rectangles[i][1] - rectangles[j][1]}"]])

            cnf.append([-variables[f"ud{i + 1},{j + 1}"], variables[f"py{i + 1},{f}"],
                        -variables.get(f"py{j + 1},{f + rectangles[i][1]}", 0)])
            cnf.append([-variables[f"ud{j + 1},{i + 1}"], variables.get(f"py{j + 1},{f}", 0),
                        -variables.get(f"py{i + 1},{f + rectangles[j][1]}", 0)])

# Domain encoding for px and py: 0 <= x <= strip[0] and 0 <= y <= strip[1]
# equal to: px(i, W-wi) ^ !px(i,-1) and py(i, H-hi) ^ !py(i,-1)

for i in range(len(rectangles)):
    cnf.append([variables[f"px{i + 1},{strip[0] - rectangles[i][0]}"]])  # px(i, W-wi)
    cnf.append([variables[f"py{i + 1},{strip[1] - rectangles[i][1]}"]])  # py(i, H-hi)

for i in range(len(rectangles)):
    for j in range(i + 1, len(rectangles)):
        # if indomain(len(px[j]) - 1, width_rects[i] - 1)
        if strip[0] - rectangles[i][0] + 1 >= rectangles[j][0] - 1:
            cnf.append([-variables[f"lr{i + 1},{j + 1}"], -variables[f"px{j + 1},{rectangles[i][0] - 1}"]])
        else:
            cnf.append([-variables[f"lr{i + 1},{j + 1}"], variables[f"px{j + 1},{strip[0] - rectangles[i][0] + 1}"]])
        # if indomain(len(px[i] - 1, width_rects[j] - 1)
        if strip[0] - rectangles[j][0] + 1 >= rectangles[i][0] - 1:
            cnf.append([-variables[f"lr{j + 1},{i + 1}"], -variables[f"px{i + 1},{rectangles[j][0] - 1}"]])
        else:
            cnf.append([-variables[f"lr{j + 1},{i + 1}"], variables[f"px{i + 1},{strip[0] - rectangles[j][0] + 1}"]])
        # if indomain(len(py[j]) - 1, height_rects[i] - 1)
        if strip[1] - rectangles[i][1] + 1 >= rectangles[j][1] - 1:
            cnf.append([-variables[f"ud{i + 1},{j + 1}"], -variables[f"py{j + 1},{rectangles[i][1] - 1}"]])
        else:
            cnf.append([-variables[f"ud{i + 1},{j + 1}"], variables[f"py{j + 1},{strip[1] - rectangles[i][1] + 1}"]])
        # if indomain(len(py[i]) - 1, height_rects[j] - 1)
        if strip[1] - rectangles[j][1] + 1 >= rectangles[i][1] - 1:
            cnf.append([-variables[f"ud{j + 1},{i + 1}"], -variables[f"py{i + 1},{rectangles[j][1] - 1}"]])
        else:
            cnf.append([-variables[f"ud{j + 1},{i + 1}"], variables[f"py{i + 1},{strip[1] - rectangles[j][1] + 1}"]])

print(cnf)

with Solver(name="mc") as solver:
    solver.append_formula(cnf)
    if solver.solve():
        model = solver.get_model()
        print("SAT")
        result = {}
        for var in model:
            if var > 0:
                result[list(variables.keys())[list(variables.values()).index(var)]] = True
            else:
                result[list(variables.keys())[list(variables.values()).index(-var)]] = False
        print(result)

        for i in range(len(rectangles)):
            for e in range(strip[0] - rectangles[i][0] + 1):
                if result[f"px{i + 1},{e}"] == False and result[f"px{i + 1},{e + 1}"] == True:
                    print(f"x{i + 1} = {e + 1}")
                if e == 0 and result[f"px{i + 1},{e}"] == True:
                    print(f"x{i + 1} = 0")
            for f in range(strip[1] - rectangles[i][1] + 1):
                if result[f"py{i + 1},{f}"] == False and result[f"py{i + 1},{f + 1}"] == True:
                    print(f"y{i + 1} = {f + 1}")
                if f == 0 and result[f"py{i + 1},{f}"] == True:
                    print(f"y{i + 1} = 0")
    else:
        print("UNSAT")