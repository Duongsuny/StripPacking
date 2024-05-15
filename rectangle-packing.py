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

def indomain(a, b):
    return a - b >= 0

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

#domain encoding for px and py


#encoding non-overlapping constraints
for i in range(1, len(rectangles)):
    for j in range(i + 1, len(rectangles) + 1):

        #domain constraint
        # if width - rectangles[j - 1].width >= rectangles[i - 1].width - 1:
        #     clauses.append([
        #         -dict["l" + str(i) + "," + str(j)],
        #         -dict["px" + str(j) + "," + str(rectangles[i - 1].width - 1)],
        #     ])
        # else:
        #     clauses.append([
        #         -dict["l" + str(i) + "," + str(j)],
        #         -dict["px" + str(j) + "," + str(width - rectangles[j - 1].width - 1)],
        #     ])
        #
        # if width - rectangles[i - 1].width >= rectangles[j - 1].width - 1:
        #     clauses.append([
        #         -dict["l" + str(j) + "," + str(i)],
        #         -dict["px" + str(i) + "," + str(rectangles[j - 1].width - 1)],
        #     ])
        # else:
        #     clauses.append([
        #         -dict["l" + str(j) + "," + str(i)],
        #         -dict["px" + str(i) + "," + str(width - rectangles[i - 1].width - 1)],
        #     ])
        #
        # if height - rectangles[j - 1].height >= rectangles[i - 1].height - 1:
        #     clauses.append([
        #         -dict["u" + str(i) + "," + str(j)],
        #         -dict["py" + str(j) + "," + str(rectangles[i - 1].height - 1)],
        #     ])
        # else:
        #     clauses.append([
        #         -dict["u" + str(i) + "," + str(j)],
        #         -dict["py" + str(j) + "," + str(height - rectangles[j - 1].height - 1)],
        #     ])
        #
        # if height - rectangles[i - 1].height >= rectangles[j - 1].height - 1:
        #     clauses.append([
        #         -dict["u" + str(j) + "," + str(i)],
        #         -dict["py" + str(i) + "," + str(rectangles[j - 1].height - 1)],
        #     ])
        # else:
        #     clauses.append([
        #         -dict["u" + str(j) + "," + str(i)],
        #         -dict["py" + str(i) + "," + str(height - rectangles[i - 1].height - 1)],
        #     ])

        #non-overlapping constraints
        clauses.append([
            dict["l" + str(i) + "," + str(j)],
            dict["l" + str(j) + "," + str(i)],
            dict["u" + str(i) + "," + str(j)],
            dict["u" + str(j) + "," + str(i)]
        ])

        # print([
        #     ("l" + str(i) + "," + str(j)),
        #     ("l" + str(j) + "," + str(i)),
        #     ("u" + str(i) + "," + str(j)),
        #     ("u" + str(j) + "," + str(i))
        # ])

        # clauses.append([
        #     -dict["l" + str(i) + "," + str(j)],
        #     dict["px" + str(i) + "," + str(width - rectangles[i - 1].width - rectangles[j - 1].width)]
        # ])
        #
        # clauses.append([
        #     -dict["l" + str(i) + "," + str(j)],
        #     -dict["px" + str(j) + "," + str(0)]
        # ])
        #
        # clauses.append([
        #     -dict["u" + str(i) + "," + str(j)],
        #     dict["py" + str(i) + "," + str(height - rectangles[i - 1].height - rectangles[j - 1].height)]
        # ])
        #
        # clauses.append([
        #     -dict["u" + str(i) + "," + str(j)],
        #     -dict["py" + str(j) + "," + str(0)]
        # ])

        for e in range(0, width - rectangles[i - 1].width):
            if e + rectangles[i - 1].width < width - rectangles[j - 1].width:
                clauses.append([
                    -dict["l" + str(i) + "," + str(j)],
                    dict["px" + str(i) + "," + str(e)],
                    -dict["px" + str(j) + "," + str(e + rectangles[i - 1].width)],
                ])

                print([
                        ("-l" + str(i) + "," + str(j)),
                        ("px" + str(i) + "," + str(e)),
                        ("-px" + str(j) + "," + str(e + rectangles[i - 1].width)),
                ])

            if e + rectangles[j - 1].width < width - rectangles[i - 1].width:
                clauses.append([
                    -dict["l" + str(j) + "," + str(i)],
                    dict["px" + str(j) + "," + str(e)],
                    -dict["px" + str(i) + "," + str(e + rectangles[j - 1].width)],
                ])

                print([
                    ("-l" + str(j) + "," + str(i)),
                    ("px" + str(j) + "," + str(e)),
                    ("-px" + str(i) + "," + str(e + rectangles[j - 1].width)),
                ])

        for f in range(0, width - rectangles[j - 1].height):
            if f + rectangles[i - 1].height < height - rectangles[j - 1].height:
                clauses.append([
                     -dict["u" + str(i) + "," + str(j)],
                     dict["py" + str(i) + "," + str(f)],
                     -dict["py" + str(j) + "," + str(f + rectangles[i - 1].height)]
                ])

                print([
                     ("-u" + str(i) + "," + str(j)),
                     ("py" + str(i) + "," + str(f)),
                     ("-py" + str(j) + "," + str(f + rectangles[i - 1].height))
                ])

            if f + rectangles[j - 1].height < height - rectangles[i - 1].height:
                clauses.append([
                    -dict["u" + str(j) + "," + str(i)],
                    dict["py" + str(j) + "," + str(f)],
                    -dict["py" + str(i) + "," + str(f + rectangles[j - 1].height)],
                ])

                print([
                    ("-u" + str(j) + "," + str(i)),
                    ("py" + str(j) + "," + str(f)),
                    ("-py" + str(i) + "," + str(f + rectangles[j - 1].height)),
                ])
        print("\n")

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