from pysat.solvers import Glucose3
class Rectangle:
    def __init__(self, width, height):
        self.width = width
        self.height = height


width = 4
height = 4

rectangles = [Rectangle(1, 2), Rectangle(1, 2), Rectangle(2, 1), Rectangle(1, 1)]
clauses = []
variables_count = 1
dict = {}

#generate p variables/order encoding
for i in range(len(rectangles)):
    rectangle = rectangles[i]
    for e in range(0, width - rectangle.width):
        clauses.append([-variables_count, variables_count+1])
        dict["px"+ str(i + 1) + "," + str(e)] = variables_count
        if e == width - rectangle.width - 1:
            dict["px" + str(i + 1) + "," + str(e + 1)] = variables_count + 1
            variables_count = variables_count + 2
        else:
            variables_count += 1

    for f in range(0, height - rectangle.height):
        clauses.append([-variables_count, variables_count+1])
        dict["py" + str(i + 1) + "," + str(f)] = variables_count
        if f == height - rectangle.height - 1:
            dict["py" + str(i + 1) + "," + str(f + 1)] = variables_count + 1
            variables_count = variables_count + 2
        else:
            variables_count += 1

#generate l variables
for i in range(len(rectangles) - 1):
    for j in range(i + 1, len(rectangles)):
        dict["l" + str(i + 1) + "," + str(j + 1)] = variables_count
        dict["l" + str(j + 1) + "," + str(i + 1)] = variables_count + 1
        variables_count += 2

#generate u variables
for i in range(len(rectangles) - 1):
    for j in range(i + 1, len(rectangles)):
        dict["u" + str(i + 1) + "," + str(j + 1)] = variables_count
        dict["u" + str(j + 1) + "," + str(i + 1)] = variables_count + 1
        variables_count += 2

def checkDict(key):
    global variables_count
    if key not in dict:
        dict[key] = variables_count
        variables_count += 1
    return dict[key]


#encoding non-overlapping constraints
for i in range(1, len(rectangles)):
    for j in range(i + 1, len(rectangles) + 1):
        clauses.append([
            checkDict("l" + str(i) + "," + str(j)),
            checkDict("l" + str(j) + "," + str(i)),
            checkDict("u" + str(i) + "," + str(j)),
            checkDict("u" + str(j) + "," + str(i))
        ])

        for e in range(0, width - rectangles[i - 1].width):
            clauses.append([
                -checkDict("l" + str(i) + "," + str(j)),
                checkDict("px" + str(i) + "," + str(e)),
                -checkDict("px" + str(j) + "," + str(e + rectangles[i - 1].width)),
            ])

            clauses.append([
                -checkDict("l" + str(j) + "," + str(i)),
                checkDict("px" + str(j) + "," + str(e)),
                -checkDict("px" + str(i) + "," + str(e + rectangles[j - 1].width)),
            ])

        for f in range(0, width - rectangles[j - 1].height):
            clauses.append([
                 -checkDict("u" + str(i) + "," + str(j)),
                 checkDict("py" + str(i) + "," + str(f)),
                 -checkDict("py" + str(j) + "," + str(f + rectangles[i - 1].height))
            ])

            clauses.append([
                -checkDict("u" + str(j) + "," + str(i)),
                checkDict("py" + str(j) + "," + str(f)),
                -checkDict("py" + str(i) + "," + str(f + rectangles[j - 1].height)),
            ])

print(dict)
print(clauses)
solver = Glucose3()
for clause in clauses:
    solver.add_clause(clause)

if solver.solve():
    model = solver.get_model()
    print(model)
else:
    print("unsat")