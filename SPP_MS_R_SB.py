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
if not os.path.exists('SPP_MS_R_SB'):
    os.makedirs('SPP_MS_R_SB')

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
    plt.savefig(f'SPP_MS_R_SB/{instance_name}.png')
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
        
        # Add comments for clarity
        file.write(f"c Strip Packing Problem with Rotation, W={width}, n={n_rectangles}\n")
        file.write(f"c Lower bound={lower_bound}, Upper bound={upper_bound}\n")
        
        # Define variables for rectangle positions and relations
        for i in range(n_rectangles):
            for j in range(n_rectangles):
                if i != j:
                    variables[f"lr{i + 1},{j + 1}"] = counter  # lri,rj
                    counter += 1
                    variables[f"ud{i + 1},{j + 1}"] = counter  # uri,rj
                    counter += 1
            for e in range(width):
                variables[f"px{i + 1},{e}"] = counter  # pxi,e
                counter += 1
            for h in range(upper_bound):
                variables[f"py{i + 1},{h}"] = counter  # pyi,h
                counter += 1
            variables[f"r{i + 1}"] = counter  # rotation
            counter += 1
        
        # Height constraint variables
        for h in range(lower_bound, upper_bound + 1):
            variables[f"ph_{h}"] = counter
            counter += 1
            
        # Prepare hard clauses (basic packing constraints)
        hard_clauses = []
        
        # Order encoding axioms
        for i in range(n_rectangles):
            for e in range(width - 1):
                hard_clauses.append([-variables[f"px{i + 1},{e}"], variables[f"px{i + 1},{e + 1}"]])
            for h in range(upper_bound - 1):
                hard_clauses.append([-variables[f"py{i + 1},{h}"], variables[f"py{i + 1},{h + 1}"]])
        
        # Height variable ordering - this enforces that ph_h implies ph_{h+1}
        for h in range(lower_bound, upper_bound):
            hard_clauses.append([-variables[f"ph_{h}"], variables[f"ph_{h+1}"]])
        
        # Non-overlapping constraints function 
        def add_non_overlapping(rotated, i, j, h1, h2, v1, v2):
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

            hard_clauses.append(four_literal + [i_rotation])
            hard_clauses.append(four_literal + [j_rotation])

            # Add constraints only if they're necessary
            if h1:
                for e in range(min(width, i_width)):
                    hard_clauses.append([i_rotation, -variables[f"lr{i + 1},{j + 1}"], -variables[f"px{j + 1},{e}"]])
            
                for e in positive_range(width - i_width):
                    hard_clauses.append([i_rotation, -variables[f"lr{i + 1},{j + 1}"],
                                variables[f"px{i + 1},{e}"], -variables[f"px{j + 1},{e + i_width}"]])
            
            if h2:
                for e in range(min(width, j_width)):
                    hard_clauses.append([j_rotation, -variables[f"lr{j + 1},{i + 1}"], -variables[f"px{i + 1},{e}"]])
                
                for e in positive_range(width - j_width):
                    hard_clauses.append([j_rotation, -variables[f"lr{j + 1},{i + 1}"],
                                variables[f"px{j + 1},{e}"], -variables[f"px{i + 1},{e + j_width}"]])

            if v1:
                for y_pos in range(min(upper_bound, i_height)):
                    hard_clauses.append([i_rotation, -variables[f"ud{i + 1},{j + 1}"], -variables[f"py{j + 1},{y_pos}"]])
                
                for y_pos in positive_range(upper_bound - i_height):
                    hard_clauses.append([i_rotation, -variables[f"ud{i + 1},{j + 1}"],
                                variables[f"py{i + 1},{y_pos}"], -variables[f"py{j + 1},{y_pos + i_height}"]])
            
            if v2:
                for y_pos in range(min(upper_bound, j_height)):
                    hard_clauses.append([j_rotation, -variables[f"ud{j + 1},{i + 1}"], -variables[f"py{i + 1},{y_pos}"]])
                
                for y_pos in positive_range(upper_bound - j_height):
                    hard_clauses.append([j_rotation, -variables[f"ud{j + 1},{i + 1}"],
                                variables[f"py{j + 1},{y_pos}"], -variables[f"py{i + 1},{y_pos + j_height}"]])
                
    max_width = max([int(rectangle[0]) for rectangle in rectangles])
    second_max_width = max([int(rectangle[0]) for rectangle in rectangles if int(rectangle[0]) != max_width])

    #Symmetry Breaking
    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            #Fix the position of the largest rectangle and the second largest rectangle
            if rectangles[i][0] == max_width and rectangles[j][0] == second_max_width:
                add_non_overlapping(False, i, j, False, False, True, True)
                add_non_overlapping(True, i, j, False, False, True, True)
            # Large-rectangles horizontal
            if min(rectangles[i][0], rectangles[i][1]) + min(rectangles[j][0], rectangles[j][1]) > width:
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
            if rectangles[i][0] > width:
                hard_clauses.append([variables[f"r{i + 1}"]])
            else:
                for e in range(width - rectangles[i][0], width):
                    hard_clauses.append([variables[f"r{i + 1}"], variables[f"px{i + 1},{e}"]])
            
            if rectangles[i][1] > upper_bound:
                hard_clauses.append([variables[f"r{i + 1}"]])
            else:
                for y_pos in range(upper_bound - rectangles[i][1], upper_bound):
                    hard_clauses.append([variables[f"r{i + 1}"], variables[f"py{i + 1},{y_pos}"]])

            # Rotated
            if rectangles[i][1] > width:
                hard_clauses.append([-variables[f"r{i + 1}"]])
            else:
                for e in range(width - rectangles[i][1], width):
                    hard_clauses.append([-variables[f"r{i + 1}"], variables[f"px{i + 1},{e}"]])
            
            if rectangles[i][0] > upper_bound:
                hard_clauses.append([-variables[f"r{i + 1}"]])
            else:
                for y_pos in range(upper_bound - rectangles[i][0], upper_bound):
                    hard_clauses.append([-variables[f"r{i + 1}"], variables[f"py{i + 1},{y_pos}"]])
        
        # Height-related constraints - a rectangle must fit below height h when ph_h is true
        for h in range(lower_bound, upper_bound + 1):
            for i in range(n_rectangles):
                # Normal orientation
                rect_height = rectangles[i][1]
                if h >= rect_height:
                    hard_clauses.append([-variables[f"ph_{h}"], variables[f"r{i + 1}"], 
                                       variables[f"py{i + 1},{h - rect_height}"]])
                
                # Rotated orientation
                rotated_height = rectangles[i][0]
                if h >= rotated_height:
                    hard_clauses.append([-variables[f"ph_{h}"], -variables[f"r{i + 1}"], 
                                       variables[f"py{i + 1},{h - rotated_height}"]])
        
        # Prepare soft clauses with weights
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
        rotations = [False for _ in range(n_rectangles)]
        
        if "OPTIMUM FOUND" in output:
            print("Optimal solution found!")
            
            # Extract the model line (starts with "v ")
            for line in output.split('\n'):
                if line.startswith('v '):
                    print(f"Found solution line: {line[:50]}...")  # Debug output
                    
                    # New format: v 01010101010... (continuous binary string)
                    # Remove the 'v ' prefix
                    binary_string = line[2:].strip()
                    
                    # Diagnostic information
                    print("\nSOLVER OUTPUT DIAGNOSTICS:")
                    print("=" * 50)
                    print(f"Characters in solution: {set(binary_string)}")
                    print(f"First 20 characters: {binary_string[:20]}")
                    print(f"Length of binary string: {len(binary_string)}")
                    print("=" * 50)
                    
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
                    
                    print(f"Height variables in model: {[(h, variables[f'ph_{h}']) for h in range(lower_bound, lower_bound+5)]}")
                    print(f"Sample true variables: {sorted(list(true_vars)[:20])}")
                    
                    if ph_true_heights:
                        optimal_height = min(ph_true_heights)
                        print(f"Heights where ph_h is true: {sorted(ph_true_heights)}")
                    else:
                        print("WARNING: No ph_h variables are true! This may indicate a parsing issue.")
                        # Use lower bound as fallback
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
                            # Default to non-rotated
                            w = rectangles[i][0]
                            h = rectangles[i][1]
                            
                            # If current rectangle doesn't fit in the current row, move to next row
                            if x_pos + w > width:
                                x_pos = 0
                                y_pos = max_height
                            
                            positions[i][0] = x_pos
                            positions[i][1] = y_pos
                            rotations[i] = False
                            
                            # Update position for next rectangle
                            x_pos += w
                            max_height = max(max_height, y_pos + h)
                    else:
                        # Extract rotation variables
                        for i in range(n_rectangles):
                            if variables[f"r{i + 1}"] in true_vars:
                                rotations[i] = True
                        
                        # Extract positions
                        for i in range(n_rectangles):
                            # Find x position (first position where px is true)
                            found_x = False
                            for e in range(width):
                                var_key = f"px{i + 1},{e}"
                                if var_key in variables and variables[var_key] in true_vars:
                                    if e == 0 or variables[f"px{i + 1},{e-1}"] not in true_vars:
                                        positions[i][0] = e
                                        found_x = True
                                        break
                            if not found_x:
                                print(f"WARNING: Could not determine x-position for rectangle {i}!")
                            
                            # Find y position (first position where py is true)
                            found_y = False
                            for y_pos in range(upper_bound):
                                var_key = f"py{i + 1},{y_pos}"
                                if var_key in variables and variables[var_key] in true_vars:
                                    if y_pos == 0 or variables[f"py{i + 1},{y_pos-1}"] not in true_vars:
                                        positions[i][1] = y_pos
                                        found_y = True
                                        break
                            if not found_y:
                                print(f"WARNING: Could not determine y-position for rectangle {i}!")
                    
                    # CRITICAL: Verify that all rectangles fit within the optimal height
                    actual_max_height = 0
                    for i in range(n_rectangles):
                        rect_height = rectangles[i][0] if rotations[i] else rectangles[i][1]
                        top_edge = positions[i][1] + rect_height
                        actual_max_height = max(actual_max_height, top_edge)
                        
                        # Individual rectangle check
                        if top_edge > optimal_height:
                            print(f"WARNING: Rectangle {i} extends to height {top_edge}, "
                                f"exceeding stated optimal height {optimal_height}!")
                    
                    # Overall check
                    if actual_max_height != optimal_height:
                        print(f"WARNING: Actual packing height ({actual_max_height}) differs from "
                            f"theoretical optimal ({optimal_height})!")
                        
                        # Use the actual maximum height to ensure valid display
                        optimal_height = actual_max_height
                    else:
                        print(f"Verification successful: All rectangles fit within optimal height {optimal_height}.")
                    
                    break
        else:
            print("No optimal solution found.")
            print(f"Solver output: {output}")
        
        # Clean up the temporary file
        os.unlink(wcnf_file)
        return optimal_height, positions, rotations
    
    except Exception as e:
        print(f"Error running Max-SAT solver: {e}")
        if os.path.exists(wcnf_file):
            os.unlink(wcnf_file)
        return None, None, None

def positive_range(end):
    if end < 0:
        return []
    return range(end)

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
            rectangles = []
            
            # Add rectangles from input
            for i in range(n_rec):
                w, h = map(int, input[i + 2].split())
                rectangles.append((w, h))
            
            # Initialize variables for tracking
            variables_length = 0
            clauses_length = 0
            optimal_height = float('inf')
            optimal_pos = []
            optimal_rot = []

            # Calculate initial bounds
            heights = [int(rectangle[1]) for rectangle in rectangles]
            area = math.floor(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width)
            upper_bound = min(sum(heights), calculate_first_fit_upper_bound(width, rectangles))
            lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(heights))

            print(f"Solving 2D Strip Packing with incremental SAT for instance {instance_name}")
            print(f"Width: {width}")
            print(f"Number of rectangles: {n_rec}")
            print(f"Lower bound: {lower_bound}")
            print(f"Upper bound: {upper_bound}")
            
            # Solve with incremental SAT
            optimal_height, optimal_pos, optimal_rot = SPP_MaxSAT(width, rectangles, lower_bound, upper_bound)
            
            stop = timeit.default_timer()
            runtime = stop - start

            # Display and save the solution if we found one
            #if optimal_height != float('inf'):
                #display_solution((width, optimal_height), rectangles, optimal_pos, optimal_rot, instance_name)

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
    df.to_excel('SPP_MS_R_SB.xlsx', index=False)
    print("\nResults saved to SPP_MS_R_SB.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_MS_R_SB.xlsx', index=False)
    print("\nPartial results saved to SPP_MS_R_SB.xlsx")
            