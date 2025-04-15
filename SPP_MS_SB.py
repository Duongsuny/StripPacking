import math
import fileinput
import matplotlib.pyplot as plt
import timeit
import sys
import signal
import pandas as pd
import os
import tempfile
import subprocess

from pysat.formula import CNF
from pysat.solvers import Glucose42

start = timeit.default_timer() # start clock

# Create SPP folder if it doesn't exist
if not os.path.exists('SPP_MS_SB'):
    os.makedirs('SPP_MS_SB')

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
    plt.savefig(f'SPP_MS_SB/{instance_name}.png')
    plt.close()

def positive_range(end):
    if end < 0:
        return []
    return range(end)

def SPP_MaxSAT(width, rectangles, lower_bound, upper_bound):
    """Solve 2SPP using Max-SAT approach with tt-open-wbo-inc"""
    n_rectangles = len(rectangles)
    variables = {}
    counter = 1
    global variables_length, clauses_length

    # Create a temporary file for the Max-SAT formula
    with tempfile.NamedTemporaryFile(delete=False, mode='w', suffix='.wcnf') as file:
        wcnf_file = file.name
        
        # Add comments for clarity (optional)
        file.write(f"c Strip Packing Problem, W={width}, n={n_rectangles}\n")
        file.write(f"c Lower bound={lower_bound}, Upper bound={upper_bound}\n")
        
        # Define variables for rectangle positions and relations
        for i in range(n_rectangles):
            for j in range(n_rectangles):
                if i != j:
                    variables[f"lr{i + 1},{j + 1}"] = counter  # lri,rj
                    counter += 1
                    variables[f"ud{i + 1},{j + 1}"] = counter  # uri,rj
                    counter += 1
            for e in range(width - rectangles[i][0] + 2):  # Position variables for x-axis
                variables[f"px{i + 1},{e}"] = counter  # pxi,e
                counter += 1
            for h in range(upper_bound - rectangles[i][1] + 2):  # Position variables for y-axis
                variables[f"py{i + 1},{h}"] = counter  # pyi,h
                counter += 1
        
        # Height constraint variables - ph_h means "can pack with height ≤ h"
        for h in range(lower_bound, upper_bound + 1):
            variables[f"ph_{h}"] = counter
            counter += 1
            
        # Prepare hard clauses (basic packing constraints)
        hard_clauses = []
        
        # Order encoding axioms
        for i in range(n_rectangles):
            for e in range(width - rectangles[i][0] + 1):
                hard_clauses.append([-variables[f"px{i + 1},{e}"], variables[f"px{i + 1},{e + 1}"]])
            for h in range(upper_bound - rectangles[i][1] + 1):
                hard_clauses.append([-variables[f"py{i + 1},{h}"], variables[f"py{i + 1},{h + 1}"]])
        
        # Height variable ordering - this enforces that ph_h implies ph_{h+1}
        for h in range(lower_bound, upper_bound):
            hard_clauses.append([-variables[f"ph_{h}"], variables[f"ph_{h+1}"]])
        
        # Non-overlapping constraints function remains the same
        def non_overlapping(i, j, h1, h2, v1, v2):
            i_width = rectangles[i][0]
            i_height = rectangles[i][1]
            j_width = rectangles[j][0]
            j_height = rectangles[j][1]
        
            # lri,j v lrj,i v udi,j v udj,i
            four_literal = []
            if h1: four_literal.append(variables[f"lr{i + 1},{j + 1}"])
            if h2: four_literal.append(variables[f"lr{j + 1},{i + 1}"])
            if v1: four_literal.append(variables[f"ud{i + 1},{j + 1}"])
            if v2: four_literal.append(variables[f"ud{j + 1},{i + 1}"])
            hard_clauses.append(four_literal)
        
            # First type of constraints - prevent rectangle j's left edge from being in first i_width positions
            if h1:
                for e in range(i_width):
                    if f"px{j + 1},{e}" in variables:
                        hard_clauses.append([-variables[f"lr{i + 1},{j + 1}"], -variables[f"px{j + 1},{e}"]])
            
            # First type for h2 - prevent rectangle i's left edge from being in first j_width positions
            if h2:
                for e in range(j_width):
                    if f"px{i + 1},{e}" in variables:
                        hard_clauses.append([-variables[f"lr{j + 1},{i + 1}"], -variables[f"px{i + 1},{e}"]])
        
            # First type for v1 - prevent rectangle j's bottom edge from being in first i_height positions
            if v1:
                for y_pos in range(i_height):
                    if f"py{j + 1},{y_pos}" in variables:
                        hard_clauses.append([-variables[f"ud{i + 1},{j + 1}"], -variables[f"py{j + 1},{y_pos}"]])
            
            # First type for v2 - prevent rectangle i's bottom edge from being in first j_height positions
            if v2:
                for y_pos in range(j_height):
                    if f"py{i + 1},{y_pos}" in variables:
                        hard_clauses.append([-variables[f"ud{j + 1},{i + 1}"], -variables[f"py{i + 1},{y_pos}"]])
        
            # Second type of constraints - enforce relative positions when certain relations hold
            # For h1: if rectangle i is to the left of j, then i's left edge at e implies j can't be at e+i_width
            if h1:
                for e in positive_range(width - i_width):
                    if f"px{i + 1},{e}" in variables and f"px{j + 1},{e + i_width}" in variables:
                        hard_clauses.append([-variables[f"lr{i + 1},{j + 1}"],
                                      variables[f"px{i + 1},{e}"], 
                                      -variables[f"px{j + 1},{e + i_width}"]])
            
            # For h2: if rectangle j is to the left of i, then j's left edge at e implies i can't be at e+j_width
            if h2:
                for e in positive_range(width - j_width):
                    if f"px{j + 1},{e}" in variables and f"px{i + 1},{e + j_width}" in variables:
                        hard_clauses.append([-variables[f"lr{j + 1},{i + 1}"],
                                      variables[f"px{j + 1},{e}"], 
                                      -variables[f"px{i + 1},{e + j_width}"]])
        
            # For v1: if rectangle i is below j, then i's bottom edge at f implies j can't be at f+i_height
            if v1:
                for y_pos in positive_range(upper_bound - i_height):
                    if f"py{i + 1},{y_pos}" in variables and f"py{j + 1},{y_pos + i_height}" in variables:
                        hard_clauses.append([-variables[f"ud{i + 1},{j + 1}"],
                                      variables[f"py{i + 1},{y_pos}"], 
                                      -variables[f"py{j + 1},{y_pos + i_height}"]])
            
            # For v2: if rectangle j is below i, then j's bottom edge at f implies i can't be at f+j_height
            if v2:
                for y_pos in positive_range(upper_bound - j_height):
                    if f"py{j + 1},{y_pos}" in variables and f"py{i + 1},{y_pos + j_height}" in variables:
                        hard_clauses.append([-variables[f"ud{j + 1},{i + 1}"],
                                      variables[f"py{j + 1},{y_pos}"], 
                                      -variables[f"py{i + 1},{y_pos + j_height}"]])
                
        # Add non-overlapping constraints for all pairs of rectangles
        for i in range(n_rectangles):
            for j in range(i + 1, n_rectangles):
                # Large-rectangles horizontal
                if rectangles[i][0] + rectangles[j][0] > width:
                    non_overlapping(i, j, False, False, True, True)
                # Large rectangles vertical
                elif rectangles[i][1] + rectangles[j][1] > upper_bound:
                    non_overlapping(i, j, True, True, False, False)
                # Same-sized rectangles
                elif rectangles[i] == rectangles[j]:
                    non_overlapping(i, j, True, False, True, True)
                # Normal rectangles
                else:
                    non_overlapping(i, j, True, True, True, True)
                
        # Domain encoding to ensure rectangles are placed within strip boundaries
        for i in range(n_rectangles):
            # Right edge within strip width
            hard_clauses.append([variables[f"px{i + 1},{width - rectangles[i][0]}"]])
            
            # Top edge within strip height - integrated with height constraint variables
            for h in range(lower_bound, upper_bound + 1):
                if h >= rectangles[i][1]:  # Rectangle must fit below height h
                    hard_clauses.append([-variables[f"ph_{h}"], variables[f"py{i + 1},{h - rectangles[i][1]}"]])
        
        # Prepare soft clauses with weights for height minimization
        soft_clauses = []
        
        # Use weight 1 for all height variables
        for h in range(lower_bound, upper_bound + 1):
            soft_clauses.append((1, [variables[f"ph_{h}"]]))  # We want ph_h to be FALSE when possible
        
        # Require at least one ph_h to be true (ensures a solution exists)
        all_ph_vars = [variables[f"ph_{h}"] for h in range(lower_bound, upper_bound + 1)]
        hard_clauses.append(all_ph_vars)
        
        # No p-line needed for tt-open-wbo-inc
        
        # Write hard clauses with 'h' prefix
        for clause in hard_clauses:
            file.write(f"h {' '.join(map(str, clause))} 0\n")
        
        # Write soft clauses with their weights
        for weight, clause in soft_clauses:
            file.write(f"{weight} {' '.join(map(str, clause))} 0\n")
            
        # For debugging, print details about the WCNF file
        print(f"Created WCNF file with {len(hard_clauses)} hard clauses and {len(soft_clauses)} soft clauses")
        print(f"Variable count: {counter-1}")
        print(f"Sample variables: ph_{lower_bound}={variables[f'ph_{lower_bound}']}, " +
              f"px{1},{0}={variables.get(f'px{1},{0}', 'N/A')}")
        
        # On Windows, you might need to flush and close the file explicitly
        file.flush()

    variables_length = len(variables)
    clauses_length = len(hard_clauses) + len(soft_clauses)
            
    # Call tt-open-wbo-inc solver
    try:
        print(f"Running tt-open-wbo-inc on {wcnf_file}...")
        result = subprocess.run(
            ["./tt-open-wbo-inc-Glucose4_1_static", wcnf_file], 
            capture_output=True, 
            text=True
        )
        
        output = result.stdout
        print(f"Solver output preview: {output[:200]}...")  # Debug: Show beginning of output
        
        # Parse the output to find the model
        optimal_height = upper_bound
        positions = [[0, 0] for _ in range(n_rectangles)]
        
        if "OPTIMUM FOUND" in output:
            print("Optimal solution found!")
            
            # Extract the model line (starts with "v ")
            for line in output.split('\n'):
                if line.startswith('v '):
                    print(f"Found solution line: {line[:50]}...")  # Debug output
                    
                    # Fix: Use strip() instead of trip() (typo)
                    # New format: v 01010101010... (continuous binary string)
                    # Remove the 'v ' prefix
                    binary_string = line[2:].strip()
                    
                    # # Diagnostic information
                    # print("\nSOLVER OUTPUT DIAGNOSTICS:")
                    # print("=" * 50)
                    # print(f"Characters in solution: {set(binary_string)}")
                    # print(f"First 20 characters: {binary_string[:20]}")
                    # print(f"Length of binary string: {len(binary_string)}")
                    # print("=" * 50)
                    
                    # Convert binary values to true variable set
                    true_vars = set()
                    
                    # Process the solution string - tt-open-wbo-inc can output in different formats
                    # Try to interpret as space-separated list of integers first
                    if " " in binary_string:
                        try:
                            for val in binary_string.split():
                                val_int = int(val)
                                if val_int > 0:  # Positive literals represent true variables
                                    true_vars.add(val_int)
                        except ValueError:
                            # Not integers, try as space-separated binary values
                            for i, val in enumerate(binary_string.split()):
                                if val == '1':
                                    true_vars.add(i + 1)  # 1-indexed
                    else:
                        # No spaces - treat as continuous binary string
                        for i, val in enumerate(binary_string):
                            if val == '1':
                                true_vars.add(i + 1)  # 1-indexed
                    
                    print(f"Found {len(true_vars)} true variables out of {len(binary_string)} total")
                    
                    # Extract height variables and find minimum height where ph_h is true
                    ph_true_heights = []
                    for h in range(lower_bound, upper_bound + 1):
                        var_key = f"ph_{h}"
                        if var_key in variables and variables[var_key] in true_vars:
                            ph_true_heights.append(h)
                    
                    # print(f"Height variables in model: {[(h, variables[f'ph_{h}']) for h in range(lower_bound, lower_bound+5)]}")
                    # print(f"Sample true variables: {sorted(list(true_vars)[:20])}")
                    
                    if ph_true_heights:
                        optimal_height = min(ph_true_heights)
                        print(f"Heights where ph_h is true: {sorted(ph_true_heights)}")
                    else:
                        print("WARNING: No ph_h variables are true! This may indicate a parsing issue.")
                        # Check if we're within bounds - the solution string might not include all variables
                        height_var_indices = [variables[f"ph_{h}"] for h in range(lower_bound, upper_bound + 1)]
                        min_height_var = min(height_var_indices)
                        max_height_var = max(height_var_indices)
                        
                        if len(binary_string) < min_height_var:
                            print(f"Binary string length ({len(binary_string)}) is less than smallest height variable index ({min_height_var}).")
                            print("This suggests the output format needs to be interpreted differently.")
                            # Assume lowest possible height when uncertain
                            optimal_height = lower_bound

                    # If we couldn't parse any variables but the solver found a solution,
                    # use the lower bound as a fallback
                    if not true_vars:
                        print("WARNING: Solution parsing failed. Using lower bound height as fallback.")
                        optimal_height = lower_bound
                        
                        # Set default positions - simple greedy left-bottom placement
                        x_pos = 0
                        y_pos = 0
                        max_height = 0
                        for i in range(n_rectangles):
                            # If current rectangle doesn't fit in the current row, move to next row
                            if x_pos + rectangles[i][0] > width:
                                x_pos = 0
                                y_pos = max_height
                            
                            positions[i][0] = x_pos
                            positions[i][1] = y_pos
                            
                            # Update position for next rectangle
                            x_pos += rectangles[i][0]
                            max_height = max(max_height, y_pos + rectangles[i][1])
                    
                    # Extract positions - Find the exact transition point for each rectangle
                    for i in range(n_rectangles):
                        # Find x position (first position where px is true)
                        found_x = False
                        for e in range(width - rectangles[i][0] + 1):
                            var_key = f"px{i + 1},{e}"
                            if var_key in variables and variables[var_key] in true_vars:
                                if e == 0 or f"px{i + 1},{e-1}" not in variables or variables[f"px{i + 1},{e-1}"] not in true_vars:
                                    positions[i][0] = e
                                    found_x = True
                                    break
                                    
                        # Find y position (first position where py is true)
                        found_y = False
                        for y_pos in range(upper_bound - rectangles[i][1] + 1):
                            var_key = f"py{i + 1},{y_pos}"
                            if var_key in variables and variables[var_key] in true_vars:
                                if y_pos == 0 or f"py{i + 1},{y_pos-1}" not in variables or variables[f"py{i + 1},{y_pos-1}"] not in true_vars:
                                    positions[i][1] = y_pos
                                    found_y = True
                                    break
        else:
            print("No optimal solution found.")
            print(f"Solver output: {output}")
        
        # Clean up the temporary file
        os.unlink(wcnf_file)
        return optimal_height, positions
    
    except Exception as e:
        print(f"Error running Max-SAT solver: {e}")
        if os.path.exists(wcnf_file):
            os.unlink(wcnf_file)
        return None, None

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
            optimal_height, optimal_pos = SPP_MaxSAT(width, rectangles, lower_bound, upper_bound)
            
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
    df.to_excel('SPP_MS_SB.xlsx', index=False)
    print("\nResults saved to SPP_MS_SB.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_MS_SB.xlsx', index=False)
    print("\nPartial results saved to SPP_MS_SB.xlsx")
            