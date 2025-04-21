import math
import signal
import sys
import os
import multiprocessing
import threading
import time

from pysat.formula import CNF
from pysat.solvers import Glucose4

import fileinput
import matplotlib.pyplot as plt
import timeit
import pandas as pd

# Create SPP folder if it doesn't exist
if not os.path.exists('SPP_R'):
    os.makedirs('SPP_R')

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

def display_solution(strip, rectangles, pos_circuits, rotations, instance_name):
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
        # Save the plot to SPP folder
    plt.savefig(f'SPP_R_SB/{instance_name}.png')
    plt.close()

def get_instances_from_c(level=None, start_level=None, end_level=None, instance=None):
    """
    Get list of instances from c folder based on parameters
    """
    instances = []
    if level is not None:
        for p in range(1, 4):
            instances.append(f"C{level}P{p}")
    elif start_level is not None and end_level is not None:
        for l in range(start_level, end_level + 1):
            for p in range(1, 4):
                instances.append(f"C{l}P{p}")
    elif instance is not None:
        instances.append(instance)
    else:
        for l in range(1, 8):
            for p in range(1, 4):
                instances.append(f"C{l}P{p}")
    return instances

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
                
    variables_length = len(variables)
    clauses_length = len(cnf.clauses)

    with Glucose4() as solver:
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
                return (["sat", pos, rotation])
            else:
                print("UNSAT")
                return ("unsat")



def SPP(lower, upper):
    global optimal_height, optimal_pos, optimal_rot
    if lower <= upper:
        mid = (lower + upper) // 2
        OPP_result = OPP((width, mid))
        if OPP_result == "unsat":
            if lower + 1 == upper:
                return -1
            else:
                return SPP(mid, upper)
        else:
            optimal_height = mid
            optimal_pos = OPP_result[1]
            optimal_rot = OPP_result[2]
            if lower + 1 == upper:
                return -1
            else:
                return SPP(lower, mid)
    else:
        return -1

# Main execution
results_data = []

try:
    for instance in range(1, 39):
        instance_name = instances[instance]
        try:
            print(f"\nProcessing instance {instance_name}")
            start = timeit.default_timer()

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
            print(optimal_pos)
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Display and save the solution if we found one
            if optimal_height != float('inf'):
                print(rectangles)
                display_solution((width, optimal_height), rectangles, optimal_pos, optimal_rot, instance_name)

            # Store results
            instance_result = {
                'Instance': instance_name,
                'Variables': variables_length,
                'Clauses': clauses_length,
                'Runtime': runtime,
                'Optimal_Height': optimal_height if optimal_height != float('inf') else 'TIMEOUT'
            }
            results_data.append(instance_result)
            
            print(f"Instance {instance_name} completed - Runtime: {runtime:.2f}s, Height: {optimal_height}")

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
    df.to_excel('SPP_R.xlsx', index=False)
    print("\nResults saved to SPP_R.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_R.xlsx', index=False)
    print("\nPartial results saved to SPP_R.xlsx")