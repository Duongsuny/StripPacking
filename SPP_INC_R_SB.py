import math
import fileinput
import matplotlib.pyplot as plt
import timeit
import sys
import signal
import pandas as pd
import os

from pysat.formula import CNF
from pysat.solvers import Glucose42

start = timeit.default_timer() # start clock

# Create SPP folder if it doesn't exist
if not os.path.exists('SPP_INC_R_SB'):
    os.makedirs('SPP_INC_R_SB')

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
    plt.savefig(f'SPP_INC_R_SB/{instance_name}.png')
    plt.close()

def positive_range(end):
    if end < 0:
        return []
    return range(end)

def SPP_Incremental_Rotation(rectangles, strip_width, lower_bound, upper_bound, timeout=1800):
    """
    Solve 2D Strip Packing with rotation using incremental SAT solving.
    Returns the optimal height, rectangle positions, and rotation states.
    """
    global variables_length, clauses_length
    n_rectangles = len(rectangles)
    
    # Initialize the CNF formula and variables
    cnf = CNF()
    variables = {}
    counter = 1
    
    # Start a timer for the timeout
    start_time = timeit.default_timer()
    
    # Create variables for rectangle positions and relations
    # lr (left-right) and ud (up-down) variables
    for i in range(n_rectangles):
        for j in range(n_rectangles):
            if i != j:
                variables[f"lr{i+1},{j+1}"] = counter  # lri,rj
                counter += 1
                variables[f"ud{i+1},{j+1}"] = counter  # udi,rj
                counter += 1
        
        # Position variables with order encoding
        for e in range(strip_width):
            variables[f"px{i+1},{e}"] = counter  # pxi,e
            counter += 1
            
        for h in range(upper_bound):
            variables[f"py{i+1},{h}"] = counter  # pyi,h
            counter += 1
        
        # Rotation variables - True means the rectangle is rotated (width↔height)
        variables[f"r{i+1}"] = counter
        counter += 1
    
    # Height variables - ph_h means "can pack with height ≤ h"
    for h in range(lower_bound, upper_bound + 1):
        variables[f"ph_{h}"] = counter
        counter += 1
    
    # Add order encoding axiom clauses
    for i in range(n_rectangles):
        # ¬pxi,e ∨ pxi,e+1
        for e in range(strip_width - 1):
            cnf.append([-variables[f"px{i+1},{e}"], variables[f"px{i+1},{e+1}"]])
        
        # ¬pyi,h ∨ pyi,h+1
        for h in range(upper_bound - 1):
            cnf.append([-variables[f"py{i+1},{h}"], variables[f"py{i+1},{h+1}"]])
    
    # Add height variable ordering constraints
    # If ph_h is true, then ph_{h+1} must also be true
    for h in range(lower_bound, upper_bound):
        cnf.append([-variables[f"ph_{h}"], variables[f"ph_{h+1}"]])
    
    # Non-overlapping constraints function
    def add_non_overlapping(rotated, i, j, h1, h2, v1, v2):
        # Get dimensions based on rotation
        if not rotated:
            i_width = rectangles[i][0]
            i_height = rectangles[i][1]
            j_width = rectangles[j][0]
            j_height = rectangles[j][1]
            i_rotation = variables[f"r{i+1}"]  # Not rotated means r{i+1} is False
            j_rotation = variables[f"r{j+1}"]  # Not rotated means r{j+1} is False
        else:
            i_width = rectangles[i][1]
            i_height = rectangles[i][0]
            j_width = rectangles[j][1]
            j_height = rectangles[j][0]
            i_rotation = -variables[f"r{i+1}"]   # Rotated means r{i+1} is True
            j_rotation = -variables[f"r{j+1}"]   # Rotated means r{j+1} is True

        # lri,j v lrj,i v udi,j v udj,i v rotation literals
        four_literal = []
        if h1: four_literal.append(variables[f"lr{i+1},{j+1}"])
        if h2: four_literal.append(variables[f"lr{j+1},{i+1}"])
        if v1: four_literal.append(variables[f"ud{i+1},{j+1}"])
        if v2: four_literal.append(variables[f"ud{j+1},{i+1}"])
        
        # Make clause only apply if rotation is correct
        cnf.append(four_literal + [i_rotation])
        cnf.append(four_literal + [j_rotation])

        # First type constraints - prevent rectangle j's left edge from being too close to i
        if h1:
            for e in range(min(strip_width, i_width)):
                cnf.append([i_rotation, -variables[f"lr{i+1},{j+1}"], -variables[f"px{j+1},{e}"]])
        
            for e in positive_range(strip_width - i_width):
                cnf.append([i_rotation, -variables[f"lr{i+1},{j+1}"],
                          variables[f"px{i+1},{e}"], 
                          -variables[f"px{j+1},{e + i_width}"]])
        
        if h2:
            for e in range(min(strip_width, j_width)):
                cnf.append([j_rotation, -variables[f"lr{j+1},{i+1}"], -variables[f"px{i+1},{e}"]])
            
            for e in positive_range(strip_width - j_width):
                cnf.append([j_rotation, -variables[f"lr{j+1},{i+1}"],
                          variables[f"px{j+1},{e}"], 
                          -variables[f"px{i+1},{e + j_width}"]])

        if v1:
            for h in range(min(upper_bound, i_height)):
                cnf.append([i_rotation, -variables[f"ud{i+1},{j+1}"], -variables[f"py{j+1},{h}"]])
            
            for h in positive_range(upper_bound - i_height):
                cnf.append([i_rotation, -variables[f"ud{i+1},{j+1}"],
                          variables[f"py{i+1},{h}"], 
                          -variables[f"py{j+1},{h + i_height}"]])
        
        if v2:
            for h in range(min(upper_bound, j_height)):
                cnf.append([j_rotation, -variables[f"ud{j+1},{i+1}"], -variables[f"py{i+1},{h}"]])
            
            for h in positive_range(upper_bound - j_height):
                cnf.append([j_rotation, -variables[f"ud{j+1},{i+1}"],
                          variables[f"py{j+1},{h}"], 
                          -variables[f"py{i+1},{h + j_height}"]])
    
    # Add non-overlapping constraints for all pairs of rectangles
    for i in range(n_rectangles):
        for j in range(i + 1, n_rectangles):
            # Large-rectangles horizontal
            if min(rectangles[i][0], rectangles[i][1]) + min(rectangles[j][0], rectangles[j][1]) > strip_width:
                add_non_overlapping(False, i, j, False, False, True, True)
                add_non_overlapping(True, i, j, False, False, True, True)
            # Large rectangles vertical
            elif min(rectangles[i][0], rectangles[i][1]) + min(rectangles[j][0], rectangles[j][1]) > upper_bound:
                add_non_overlapping(False, i, j, True, True, False, False)
                add_non_overlapping(True, i, j, True, True, False, False)
            # Normal rectangles
            else:
                add_non_overlapping(False, i, j, True, True, True, True)
                add_non_overlapping(True, i, j, True, True, True, True)
    
    # Domain encoding to ensure every rectangle stays inside strip's boundary
    for i in range(n_rectangles):
        # Width checks - normal orientation
        if rectangles[i][0] > strip_width:
            cnf.append([variables[f"r{i+1}"]])  # Must be rotated if width > strip_width
        else:
            for e in range(strip_width - rectangles[i][0], strip_width):
                cnf.append([variables[f"r{i+1}"], variables[f"px{i+1},{e}"]])
        
        # Height checks - normal orientation
        if rectangles[i][1] > upper_bound:
            cnf.append([variables[f"r{i+1}"]])  # Must be rotated if height > upper_bound
        else:
            for h in range(upper_bound - rectangles[i][1], upper_bound):
                cnf.append([variables[f"r{i+1}"], variables[f"py{i+1},{h}"]])

        # Width checks - rotated orientation
        if rectangles[i][1] > strip_width:
            cnf.append([-variables[f"r{i+1}"]])  # Cannot be rotated if rotated_width > strip_width
        else:
            for e in range(strip_width - rectangles[i][1], strip_width):
                cnf.append([-variables[f"r{i+1}"], variables[f"px{i+1},{e}"]])
        
        # Height checks - rotated orientation
        if rectangles[i][0] > upper_bound:
            cnf.append([-variables[f"r{i+1}"]])  # Cannot be rotated if rotated_height > upper_bound
        else:
            for h in range(upper_bound - rectangles[i][0], upper_bound):
                cnf.append([-variables[f"r{i+1}"], variables[f"py{i+1},{h}"]])
    
    # Height constraints - connecting ph_h with rectangle positions
    for h in range(lower_bound, upper_bound + 1):
        for i in range(n_rectangles):
            # Normal orientation
            rect_height = rectangles[i][1]
            if h >= rect_height:
                cnf.append([-variables[f"ph_{h}"], variables[f"r{i+1}"], 
                          variables[f"py{i+1},{h - rect_height}"]])
            
            # Rotated orientation
            rotated_height = rectangles[i][0]
            if h >= rotated_height:
                cnf.append([-variables[f"ph_{h}"], -variables[f"r{i+1}"], 
                          variables[f"py{i+1},{h - rotated_height}"]])
                
    variables_length = len(variables)
    clauses_length = len(cnf.clauses)
    
    # Initialize the incremental SAT solver with the CNF formula
    with Glucose42(bootstrap_with=cnf) as solver:
        optimal_height = upper_bound
        positions = None
        rotations = [False] * n_rectangles
        
        # For model reuse (as described in the paper)
        best_model = None
        
        # Binary search with incremental solving
        current_lb = lower_bound
        current_ub = upper_bound
        
        while current_lb <= current_ub:
            # Check timeout
            if timeit.default_timer() - start_time > timeout:
                print(f"Timeout after {timeout} seconds")
                break
            
            mid = (current_lb + current_ub) // 2
            print(f"Trying height: {mid} (lower={current_lb}, upper={current_ub})")
            
            # Set up assumptions for this iteration - test if we can pack with height ≤ mid
            assumptions = [variables[f"ph_{mid}"]]
            
            # Solve with assumptions
            is_sat = solver.solve(assumptions=assumptions)
            
            if is_sat:
                # We found a solution with height ≤ mid
                optimal_height = mid
                
                # Save the model for reuse
                best_model = solver.get_model()
                
                # Extract positions and rotations from the model
                positions = [[0, 0] for _ in range(n_rectangles)]
                rotations = [False for _ in range(n_rectangles)]
                
                # Convert model to dictionary for faster lookup
                true_vars = set(var for var in best_model if var > 0)
                
                # Extract rotation variables
                for i in range(n_rectangles):
                    rotations[i] = variables[f"r{i+1}"] in true_vars
                
                # Extract positions
                for i in range(n_rectangles):
                    # Find x position (first position where px is true)
                    found_x = False
                    for e in range(strip_width + 1):
                        var = variables.get(f"px{i+1},{e}", None)
                        if var in true_vars:
                            if e == 0 or variables[f"px{i+1},{e-1}"] not in true_vars:
                                positions[i][0] = e
                                found_x = True
                                break
                    if not found_x:
                        print(f"WARNING: Could not determine x-position for rectangle {i}!")
                    
                    # Find y position (first position where py is true)
                    found_y = False
                    for y in range(upper_bound + 1):
                        var = variables.get(f"py{i+1},{y}", None)
                        if var in true_vars:
                            if y == 0 or variables[f"py{i+1},{y-1}"] not in true_vars:
                                positions[i][1] = y
                                found_y = True
                                break
                    if not found_y:
                        print(f"WARNING: Could not determine y-position for rectangle {i}!")
                
                # Verify positions and height
                actual_max_height = 0
                for i in range(n_rectangles):
                    rect_height = rectangles[i][0] if rotations[i] else rectangles[i][1]
                    top_edge = positions[i][1] + rect_height
                    actual_max_height = max(actual_max_height, top_edge)
                    
                    # Verify the actual height doesn't exceed what we're testing
                    if top_edge > mid:
                        print(f"WARNING: Rectangle {i} extends to height {top_edge}, exceeding mid={mid}")
                
                print(f"Found valid packing with height: {actual_max_height}")
                
                # Update search range - try lower height
                current_ub = mid - 1
            else:
                # No solution with height ≤ mid
                current_lb = mid + 1
        
        # Final validation of the solution
        if positions is None:
            return None, None, None
        
        actual_max_height = 0
        for i in range(n_rectangles):
            rect_height = rectangles[i][0] if rotations[i] else rectangles[i][1]
            top_edge = positions[i][1] + rect_height
            actual_max_height = max(actual_max_height, top_edge)
        
        if actual_max_height > optimal_height:
            print(f"WARNING: Actual max height {actual_max_height} exceeds optimal_height {optimal_height}")
            optimal_height = actual_max_height
        
        print(f"Final optimal height: {optimal_height}")
        return optimal_height, positions, rotations


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

# Main execution
results_data = []

try:
    instances_to_run = get_instances_from_c()

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
                    rectangles.append(rect)
                else:
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

            print(f"Solving 2D Strip Packing with incremental SAT for instance {instance_name}")
            print(f"Width: {width}")
            print(f"Number of rectangles: {n_rec}")
            print(f"Lower bound: {lower_bound}")
            print(f"Upper bound: {upper_bound}")
            
            # Solve with incremental SAT
            optimal_height, optimal_pos, optimal_rot = SPP_Incremental_Rotation(rectangles, width, lower_bound, upper_bound)
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Display and save the solution if we found one
            if optimal_height != float('inf'):
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
    df.to_excel('SPP_INC_R_SB.xlsx', index=False)
    print("\nResults saved to SPP_INC_R_SB.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_INC_R_SB.xlsx', index=False)
    print("\nPartial results saved to SPP_INC_R_SB.xlsx")
            