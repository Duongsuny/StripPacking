import math
import signal

from pysat.formula import CNF
from pysat.solvers import Glucose42

import fileinput
import matplotlib.pyplot as plt
import timeit
import pandas as pd

start = timeit.default_timer() #start the clock

# Initialize the CNF formula

#read file
def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

def display_solution(strip, rectangles, pos_circuits):
    # define Matplotlib figure and axis
    fig, ax = plt.subplots()
    ax = plt.gca()
    plt.title(strip)

    if len(pos_circuits) > 0:
        for i in range(len(rectangles)):
            rect = plt.Rectangle(pos_circuits[i], *rectangles[i], edgecolor="#333")
            ax.add_patch(rect)

    ax.set_xlim(0, strip[0])
    ax.set_ylim(0, strip[1] + 1)
    ax.set_xticks(range(strip[0] + 1))
    ax.set_yticks(range(strip[1] + 1))
    ax.set_xlabel('width')
    ax.set_ylabel('height')
    # display plot
    plt.show()

#read file input
input = read_file_instance(20) #change the instance here (instance 0 - 40)
width = int(input[0])
n_rec = int(input[1])
rectangles =  [[int(val) for val in i.split()] for i in input[-n_rec:]]
global variables_length, clauses_length
variables_length = 0
clauses_length = 0
#print(rectangles)


def positive_range(end):
    if (end < 0):
        return []
    return range(end)

def OPP(strip):
    global variables_length, clauses_length
    # Define the variables
    cnf = CNF()
    width = strip[0]
    height = strip[1]
    variables = {}
    counter = 1

    # find max height and width rectangles for largest rectangle symmetry breaking
    max_height = max([int(rectangle[1]) for rectangle in rectangles])
    max_width = max([int(rectangle[0]) for rectangle in rectangles])

    # create lr, ud variables
    for i in range(len(rectangles)):
        for j in range(len(rectangles)):
            variables[f"lr{i + 1},{j + 1}"] = counter  # lri,rj
            counter += 1
            variables[f"ud{i + 1},{j + 1}"] = counter  # uri,rj
            counter += 1
        for e in positive_range(width - rectangles[i][0] + 2):
            variables[f"px{i + 1},{e}"] = counter  # pxi,e
            counter += 1
        for f in positive_range(height - rectangles[i][1] + 2):
            variables[f"py{i + 1},{f}"] = counter  # pyi,f
            counter += 1

    # Add the 2-literal axiom clauses (order constraint)
    for i in range(len(rectangles)):
       # ¬pxi,e ∨ pxi,e+1
        for e in range(width - rectangles[i][0] + 1):  # -1 because we're using e+1 in the clause
            cnf.append([-variables[f"px{i + 1},{e}"],
                        variables[f"px{i + 1},{e + 1}"]])
        #  ¬pyi,f ∨ pxi,f+1
        for f in range(height - rectangles[i][1] + 1):  # -1 because we're using f+1 in the clause
            cnf.append([-variables[f"py{i + 1},{f}"],
                        variables[f"py{i + 1},{f + 1}"]])


    # Add the 3-literal non-overlapping constraints
    def non_overlapping(i, j, h1, h2, v1, v2):
        i_width = rectangles[i][0]
        i_height = rectangles[i][1]
        j_width = rectangles[j][0]
        j_height = rectangles[j][1]

        # lri, j ∨ lrj, i ∨ udi, j ∨ udj, i
        four_literal = []
        if h1: four_literal.append(variables[f"lr{i + 1},{j + 1}"])
        if h2: four_literal.append(variables[f"lr{j + 1},{i + 1}"])
        if v1: four_literal.append(variables[f"ud{i + 1},{j + 1}"])
        if v2: four_literal.append(variables[f"ud{j + 1},{i + 1}"])
        cnf.append(four_literal)

        # ¬lri, j ∨ ¬pxj, e
        if h1:
            for e in range(i_width):
                if f"px{j + 1},{e}" in variables:
                    cnf.append([-variables[f"lr{i + 1},{j + 1}"],
                                -variables[f"px{j + 1},{e}"]])
        # ¬lrj,i ∨ ¬pxi,e
        if h2:
            for e in range(j_width):
                if f"px{i + 1},{e}" in variables:
                    cnf.append([-variables[f"lr{j + 1},{i + 1}"],
                                -variables[f"px{i + 1},{e}"]])
        # ¬udi,j ∨ ¬pyj,f
        if v1:
            for f in range(i_height):
                if f"py{j + 1},{f}" in variables:
                    cnf.append([-variables[f"ud{i + 1},{j + 1}"],
                                -variables[f"py{j + 1},{f}"]])
        # ¬udj, i ∨ ¬pyi, f,
        if v2:
            for f in range(j_height):
                if f"py{i + 1},{f}" in variables:
                    cnf.append([-variables[f"ud{j + 1},{i + 1}"],
                                -variables[f"py{i + 1},{f}"]])

        for e in positive_range(width - i_width):
            # ¬lri,j ∨ ¬pxj,e+wi ∨ pxi,e
            if h1:
                if f"px{j + 1},{e + i_width}" in variables:
                    cnf.append([-variables[f"lr{i + 1},{j + 1}"],
                                variables[f"px{i + 1},{e}"],
                                -variables[f"px{j + 1},{e + i_width}"]])
            # ¬lrj,i ∨ ¬pxi,e+wj ∨ pxj,e
            if h2:
                if f"px{i + 1},{e + j_width}" in variables:
                    cnf.append([-variables[f"lr{j + 1},{i + 1}"],
                                variables[f"px{j + 1},{e}"],
                                -variables[f"px{i + 1},{e + j_width}"]])

        for f in positive_range(height - i_height):
            # udi,j ∨ ¬pyj,f+hi ∨ pxi,e
            if v1:
                if f"py{j + 1},{f + i_height}" in variables:
                    cnf.append([-variables[f"ud{i + 1},{j + 1}"],
                                variables[f"py{i + 1},{f}"],
                                -variables[f"py{j + 1},{f + i_height}"]])
            # ¬udj,i ∨ ¬pyi,f+hj ∨ pxj,f
            if v2:
                if f"py{i + 1},{f + j_height}" in variables:
                    cnf.append([-variables[f"ud{j + 1},{i + 1}"],
                                variables[f"py{j + 1},{f}"],
                                -variables[f"py{i + 1},{f + j_height}"]])

    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            # lri,j ∨ lrj,i ∨ udi,j ∨ udj,i
            #Large-rectangles horizontal
            if rectangles[i][0] + rectangles[j][0] > width:
                non_overlapping(i, j, False, False, True, True)

            #Large-rectangles vertical
            if rectangles[i][1] + rectangles[j][1] > height:
                non_overlapping(i, j, True, True, False, False)

            #Same-sized rectangles
            elif rectangles[i] == rectangles[j]:
                non_overlapping(i, j, True, False, True, True)
            #
            #largest width rectangle
            elif rectangles[i][0] == max_width and rectangles[j][0] > (width - max_width) / 2:
                non_overlapping(i, j, False, True, True, True)
            #
            #largest height rectangle
            elif rectangles[i][1] == max_height and rectangles[j][1] > (height - max_height) / 2:
                non_overlapping(i, j, True, True, False, True)

           #normal rectangles
            else:
                non_overlapping(i, j, True, True, True, True)



    # Domain encoding for px and py: 0 <= x <= width and 0 <= y <= height
    # equal to: px(i, W-wi) ^ !px(i,-1) and py(i, H-hi) ^ !py(i,-1)

    for i in range(len(rectangles)):
        cnf.append([variables[f"px{i + 1},{width - rectangles[i][0]}"]])  # px(i, W-wi)
        cnf.append([variables[f"py{i + 1},{height - rectangles[i][1]}"]])  # py(i, H-hi)


    # add all clauses to SAT solver
    with Glucose42() as solver:
        solver.append_formula(cnf)
        variables_length = len(variables)
        clauses_length = len(cnf.clauses)
        
        is_sat = solver.solve()
        if is_sat:
            pos = [[0 for i in range(2)] for j in range(len(rectangles))]
            model = solver.get_model()
            print("SAT")
            result = {}
            for var in model:
                if var > 0:
                    result[list(variables.keys())[list(variables.values()).index(var)]] = True
                else:
                    result[list(variables.keys())[list(variables.values()).index(-var)]] = False
            #print(result)

            # from SAT result, decode into rectangles' position
            for i in range(len(rectangles)):
                for e in range(width - rectangles[i][0] + 1):
                    if result[f"px{i + 1},{e}"] == False and result[f"px{i + 1},{e + 1}"] == True:
                        pos[i][0] = e + 1
                    if e == 0 and result[f"px{i + 1},{e}"] == True:
                        pos[i][0] = 0
                for f in range(height - rectangles[i][1] + 1):
                    if result[f"py{i + 1},{f}"] == False and result[f"py{i + 1},{f + 1}"] == True:
                        pos[i][1] = f + 1
                    if f == 0 and result[f"py{i + 1},{f}"] == True:
                        pos[i][1] = 0
            return(["sat", pos])
        else:
            print("UNSAT")
            return("unsat")


#solving 2SPP
heights = [int(rectangle[1]) for rectangle in rectangles]
area = math.floor(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width)
upper_bound = sum(heights)
lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(heights))
global optimal_height
optimal_height = 0
optimal_pos = []


# SPP searches for optimal height by repeatedly solving OPP with bisection method
def SPP(lower, upper):
    global optimal_height, optimal_pos
    if lower <= upper:
        mid = (lower + upper) // 2
        print(f"Trying height: {mid} (lower={lower}, upper={upper})")
        OPP_result = OPP((width, mid))
        if OPP_result == "unsat":
            if lower + 1 == upper:
                return -1
            else:
                SPP(mid, upper)
        else:
            optimal_height = mid
            optimal_pos = OPP_result[1]
            if lower + 1 == upper:
                return -1
            else:
                SPP(lower, mid)
    return optimal_height

# Add this timeout handler function
def timeout_handler(signum, frame):
    raise TimeoutError("Timeout reached (300s)")

# Main execution
results_data = []

try:  # Add outer try-except block for KeyboardInterrupt
    for instance in [38, 39]:  # Run specific instances 33, 38, and 40
        try:
            print(f"\nProcessing instance {instance}")
            start = timeit.default_timer()

            # Set timeout of 300 seconds (5 minutes)
            signal.signal(signal.SIGALRM, timeout_handler)
            signal.alarm(10)  # 300 secondủ

            # read file input
            input = read_file_instance(instance)
            width = int(input[0])
            n_rec = int(input[1])
            rectangles = [[int(val) for val in i.split()] for i in input[-n_rec:]]
            
            # Initialize variables for tracking
            variables_length = 0
            clauses_length = 0
            optimal_height = float('inf')
            optimal_pos = []

            # Calculate initial bounds
            heights = [int(rectangle[1]) for rectangle in rectangles]
            area = math.floor(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width)
            upper_bound = sum(heights)
            lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(heights))

            # Run SPP
            final_height = SPP(lower_bound, upper_bound)
            
            # Disable the alarm after successful completion
            signal.alarm(0)
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Store results
            instance_result = {
                'Instance': instance,
                'Variables': variables_length,
                'Clauses': clauses_length,
                'Runtime': runtime,
                'Optimal_Height': optimal_height if optimal_height != float('inf') else 'TIMEOUT/ERROR'
            }
            results_data.append(instance_result)
            
            print(f"Instance {instance} completed - Runtime: {runtime:.2f}s, Height: {optimal_height}")

        except TimeoutError as e:
            signal.alarm(0)  # Disable the alarm
            print(f"Instance {instance}: {str(e)}")
            results_data.append({
                'Instance': instance,
                'Variables': variables_length,
                'Clauses': clauses_length,
                'Runtime': '300+',
                'Optimal_Height': 'TIMEOUT'
            })
            continue
        except Exception as e:
            signal.alarm(0)  # Disable the alarm
            print(f"Error in instance {instance}: {str(e)}")
            results_data.append({
                'Instance': instance,
                'Variables': 'ERROR',
                'Clauses': 'ERROR',
                'Runtime': 'ERROR',
                'Optimal_Height': 'ERROR'
            })
            continue

    # Save results to Excel
    df = pd.DataFrame(results_data)
    df.to_excel('SPP.xlsx', index=False)
    print("\nResults saved to SPP.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    # Optionally save partial results
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_partial.xlsx', index=False)
    print("\nPartial results saved to SPP_partial.xlsx")