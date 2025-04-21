import math
import os

from pysat.formula import CNF
from pysat.solvers import Glucose42

import fileinput
import matplotlib.pyplot as plt
import timeit
import pandas as pd

# Create SPP folder if it doesn't exist
if not os.path.exists('SPP_SB_C2'):
    os.makedirs('SPP_SB_C2')

def display_solution(strip, rectangles, pos_circuits, instance_name):
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
    
    # Save the plot to SPP folder
    plt.savefig(f'SPP_SB_C2/{instance_name}.png')
    plt.close()

def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

instances= [ "",
  "HT01(c1p1)", "HT02(c1p2)", "HT03(c1p3)", "HT04(c2p1)", "HT05(c2p2)", "HT06(c2p3)", 
  "HT07(c3p1)", "HT08(c3p2)", "HT09(c3p3)", 
  "CGCUT01", "CGCUT02", "CGCUT03", 
  "GCUT01", "GCUT02", "GCUT03", "GCUT04", 
  "NGCUT01", "NGCUT02", "NGCUT03", "NGCUT04", "NGCUT05", "NGCUT06", "NGCUT07", 
  "NGCUT08", "NGCUT09", "NGCUT10", "NGCUT11", "NGCUT12", 
  "BENG01", "BENG02", "BENG03", "BENG04", "BENG05", "BENG06", "BENG07", "BENG08", "BENG09", "BENG10"
]

def calculate_first_fit_upper_bound(width, rectangles):
    # Sort rectangles by height (non-increasing)
    sorted_rects = sorted(rectangles, key=lambda r: -r[1])
    levels = []  # (y-position, remaining_width)
    
    for w, h in sorted_rects:
        # Try to place on existing level
        placed = False
        for i in range(len(levels)):
            if levels[i][1] >= w:
                levels[i] = (levels[i][0], levels[i][1] - w)
                placed = True
                break
        
        # Create new level if needed
        if not placed:
            y_pos = 0 if not levels else max(level[0] + sorted_rects[i][1] for i, level in enumerate(levels))
            levels.append((y_pos, width - w))
    
    # Calculate total height
    if not levels:
        return 0
        
    return max(level[0] + sorted_rects[levels.index(level)][1] for level in levels)

def positive_range(end):
    if end < 0:
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

    # create lr, ud variables
    for i in range(len(rectangles)):
        for j in range(len(rectangles)):
            variables[f"lr{i + 1},{j + 1}"] = counter
            counter += 1
            variables[f"ud{i + 1},{j + 1}"] = counter
            counter += 1
        for e in positive_range(width - rectangles[i][0] + 2):
            variables[f"px{i + 1},{e}"] = counter
            counter += 1
        for f in positive_range(height - rectangles[i][1] + 2):
            variables[f"py{i + 1},{f}"] = counter
            counter += 1

    # Add the 2-literal axiom clauses (order constraint)
    for i in range(len(rectangles)):
        for e in range(width - rectangles[i][0] + 1):
            cnf.append([-variables[f"px{i + 1},{e}"],
                        variables[f"px{i + 1},{e + 1}"]])
        for f in range(height - rectangles[i][1] + 1):
            cnf.append([-variables[f"py{i + 1},{f}"],
                        variables[f"py{i + 1},{f + 1}"]])

    # Add the 3-literal non-overlapping constraints
    def non_overlapping(i, j, h1, h2, v1, v2):
        i_width = rectangles[i][0]
        i_height = rectangles[i][1]
        j_width = rectangles[j][0]
        j_height = rectangles[j][1]

        four_literal = []
        if h1: four_literal.append(variables[f"lr{i + 1},{j + 1}"])
        if h2: four_literal.append(variables[f"lr{j + 1},{i + 1}"])
        if v1: four_literal.append(variables[f"ud{i + 1},{j + 1}"])
        if v2: four_literal.append(variables[f"ud{j + 1},{i + 1}"])
        cnf.append(four_literal)

        if h1:
            for e in range(i_width):
                if f"px{j + 1},{e}" in variables:
                    cnf.append([-variables[f"lr{i + 1},{j + 1}"],
                                -variables[f"px{j + 1},{e}"]])
        if h2:
            for e in range(j_width):
                if f"px{i + 1},{e}" in variables:
                    cnf.append([-variables[f"lr{j + 1},{i + 1}"],
                                -variables[f"px{i + 1},{e}"]])
        if v1:
            for f in range(i_height):
                if f"py{j + 1},{f}" in variables:
                    cnf.append([-variables[f"ud{i + 1},{j + 1}"],
                                -variables[f"py{j + 1},{f}"]])
        if v2:
            for f in range(j_height):
                if f"py{i + 1},{f}" in variables:
                    cnf.append([-variables[f"ud{j + 1},{i + 1}"],
                                -variables[f"py{i + 1},{f}"]])

        for e in positive_range(width - i_width):
            if h1 and f"px{j + 1},{e + i_width}" in variables:
                cnf.append([-variables[f"lr{i + 1},{j + 1}"],
                            variables[f"px{i + 1},{e}"],
                            -variables[f"px{j + 1},{e + i_width}"]])
            if h2 and f"px{i + 1},{e + j_width}" in variables:
                cnf.append([-variables[f"lr{j + 1},{i + 1}"],
                            variables[f"px{j + 1},{e}"],
                            -variables[f"px{i + 1},{e + j_width}"]])

        for f in positive_range(height - i_height):
            if v1 and f"py{j + 1},{f + i_height}" in variables:
                cnf.append([-variables[f"ud{i + 1},{j + 1}"],
                            variables[f"py{i + 1},{f}"],
                            -variables[f"py{j + 1},{f + i_height}"]])
            if v2 and f"py{i + 1},{f + j_height}" in variables:
                cnf.append([-variables[f"ud{j + 1},{i + 1}"],
                            variables[f"py{j + 1},{f}"],
                            -variables[f"py{i + 1},{f + j_height}"]])
        
    # find max height and width rectangles for largest rectangle symmetry breaking
    max_height = max([int(rectangle[1]) for rectangle in rectangles])
    max_width = max([int(rectangle[0]) for rectangle in rectangles])
    second_max_width = max([int(rectangle[0]) for rectangle in rectangles if int(rectangle[0]) != max_width])

    # Symmetry Breaking - Config 2
    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            #Fix the position of the largest rectangle and the second largest rectangle
            if rectangles[i][0] == max_width and rectangles[j][0] == second_max_width:
                non_overlapping(i, j, True, False, True, False)
            # Large-rectangles horizontal
            if rectangles[i][0] + rectangles[j][0] > width:
                non_overlapping(i, j, False, False, True, True)
            # Large-rectangles vertical
            elif rectangles[i][1] + rectangles[j][1] > height:
                non_overlapping(i, j, True, True, False, False)
            # Same-sized rectangles
            elif rectangles[i] == rectangles[j]:
                non_overlapping(i, j, True, False, True, True)
            else:
                non_overlapping(i, j, True, True, True, True)

    for i in range(len(rectangles)):
        cnf.append([variables[f"px{i + 1},{width - rectangles[i][0]}"]])
        cnf.append([variables[f"py{i + 1},{height - rectangles[i][1]}"]])

    variables_length = len(variables)
    clauses_length = len(cnf.clauses)

    with Glucose42() as solver:
            solver.append_formula(cnf)
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
                return ["sat", pos]
            else:
                print("UNSAT")
                return "unsat"



def SPP(lower, upper):
    global optimal_height, optimal_pos
    if lower <= upper:
        mid = (lower + upper) // 2
        print(f"Trying height: {mid} (lower={lower}, upper={upper})")
        OPP_result = OPP((width, mid))
        if OPP_result == "unsat" or OPP_result == "timeout":
            if lower + 1 == upper:
                return -1
            else:
                return SPP(mid, upper)
        else:
            optimal_height = mid
            optimal_pos = OPP_result[1]
            if lower + 1 == upper:
                return -1
            else:
                return SPP(lower, mid)
    return optimal_height

# Main execution
results_data = []

try:
    for instance_name in range(1, 39):
        try:
            print(f"\nProcessing instance {instances[instance_name]}")
            start = timeit.default_timer()

            # read file input
            input = read_file_instance(instance_name)
            width = int(input[0])
            n_rec = int(input[1])
            rectangles = []
            for i in range(2, 2 + n_rec):
                if i < len(input):
                    rect = [int(val) for val in input[i].split()]
                    rectangles.append(rect)
            
            # Initialize variables for tracking
            variables_length = 0
            clauses_length = 0
            optimal_height = float('inf')
            optimal_pos = []

            # Calculate initial bounds
            heights = [int(rectangle[1]) for rectangle in rectangles]
            area = math.floor(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width)
            upper_bound = min(sum(heights), calculate_first_fit_upper_bound(width, rectangles))
            lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(heights))

            # Run SPP
            final_height = SPP(lower_bound, upper_bound)
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Display and save the solution if we found one
            # if optimal_height != float('inf'):
            #     display_solution((width, optimal_height), rectangles, optimal_pos, instance_name)

            # Store results
            instance_result = {
                'Instance': instances[instance_name],
                'Variables': variables_length,
                'Clauses': clauses_length,
                'Runtime': runtime,
                'Optimal_Height': optimal_height if optimal_height != float('inf') else 'TIMEOUT'
            }
            results_data.append(instance_result)
            
            print(f"Instance {instances[instance_name]} completed - Runtime: {runtime:.2f}s, Height: {optimal_height}")

        except Exception as e:
            print(f"Error in instance {instance_name}: {str(e)}")
            results_data.append({
                'Instance': instance_name,
                'Variables': 'ERROR',
                'Clauses': 'ERROR',
                'Runtime': 'ERROR',
                'Optimal_Height': 'ERROR'
            })
            continue

    # Save results to Excel
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_SB_C2.xlsx', index=False)
    print("\nResults saved to SPP_SB_C2.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_SB_C2.xlsx', index=False)
    print("\nPartial results saved to SPP_SB_C2.xlsx")