import math
import signal
import sys
import os
import multiprocessing
import threading
import time

from pysat.formula import CNF
from pysat.solvers import Glucose42

import fileinput
import matplotlib.pyplot as plt
import timeit
import pandas as pd

# Create SPP folder if it doesn't exist
if not os.path.exists('SPP_SB'):
    os.makedirs('SPP_SB')

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
    plt.savefig(f'SPP/{instance_name}.png')
    plt.close()

def read_file_instance(instance_name):
    """
    Read file from c folder
    instance_name: name of the instance (e.g., "C1P1")
    """
    s = ''
    filepath = f"c/{instance_name}.txt"
    for line in fileinput.input(files=filepath):
        s += line
    # Split lines and remove any empty strings
    lines = [line.strip() for line in s.splitlines() if line.strip()]
    print(f"Debug - Reading {instance_name}:")
    print(f"Number of lines: {len(lines)}")
    print(f"First line: {lines[0]}")
    print(f"Second line: {lines[1]}")
    print(f"Last line: {lines[-1]}")
    return lines

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

def run_solver(cnf, variables, rectangles, width, height, result_queue):
    try:
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
                result_queue.put(["sat", pos])
            else:
                print("UNSAT")
                result_queue.put("unsat")
    except Exception as e:
        print(f"Solver error: {str(e)}")
        result_queue.put("error")

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

    # Symmetry Breaking
    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            # Large-rectangles horizontal
            if rectangles[i][0] + rectangles[j][0] > width:
                non_overlapping(i, j, False, False, True, True)
            # Large-rectangles vertical
            elif rectangles[i][1] + rectangles[j][1] > height:
                non_overlapping(i, j, True, True, False, False)
            # Same-sized rectangles
            elif rectangles[i] == rectangles[j]:
                non_overlapping(i, j, True, False, True, True)
            # Large-rectangles horizontal symmetry breaking
            elif rectangles[i][0] == max_width and rectangles[j][0] > (width - max_width) / 2:
                non_overlapping(i, j, False, True, True, True)
            # Large-rectangles vertical symmetry breaking
            elif rectangles[i][1] == max_height and rectangles[j][1] > (height - max_height) / 2:
                non_overlapping(i, j, True, True, False, True)
            else:
                non_overlapping(i, j, True, True, True, True)

    for i in range(len(rectangles)):
        cnf.append([variables[f"px{i + 1},{width - rectangles[i][0]}"]])
        cnf.append([variables[f"py{i + 1},{height - rectangles[i][1]}"]])

    variables_length = len(variables)
    clauses_length = len(cnf.clauses)

    # Create a queue for the result
    result_queue = multiprocessing.Queue()
    
    # Create a process for running the solver
    process = multiprocessing.Process(target=run_solver, args=(cnf, variables, rectangles, width, height, result_queue))
    process.start()
    
    # Wait for 600 seconds
    process.join(timeout=600)
    
    # If process is still alive after timeout, terminate it
    if process.is_alive():
        process.terminate()
        process.join()
        print(f"TIMEOUT for height {height}")
        return "timeout"
    
    try:
        # Get the result from the queue
        return result_queue.get(timeout=1)
    except:
        return "timeout"

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
    instances_to_run = get_instances_from_c(level=1)

    for instance_name in instances_to_run:
        try:
            print(f"\nProcessing instance {instance_name}")
            start = timeit.default_timer()

            # read file input
            input = read_file_instance(instance_name)
            width = int(input[0])
            n_rec = int(input[1])
            print(f"Debug - Width: {width}, Number of rectangles: {n_rec}")
            print(f"Debug - Input length: {len(input)}, Expected rectangles: {n_rec}")
            rectangles = []
            for i in range(2, 2 + n_rec):
                if i < len(input):
                    rect = [int(val) for val in input[i].split()]
                    print(f"Debug - Rectangle {i-1}: {rect}")
                    rectangles.append(rect)
                else:
                    print(f"Error - Missing rectangle data at line {i}")
                    raise IndexError(f"Missing rectangle data at line {i}")
            
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
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Display and save the solution if we found one
            if optimal_height != float('inf'):
                display_solution((width, optimal_height), rectangles, optimal_pos, instance_name)

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
    df.to_excel('SPP_SB.xlsx', index=False)
    print("\nResults saved to SPP_SB.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_SB.xlsx', index=False)
    print("\nPartial results saved to SPP_SB.xlsx")