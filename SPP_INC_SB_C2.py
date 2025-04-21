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
if not os.path.exists('SPP_INC_SB_C2'):
    os.makedirs('SPP_INC_SB_C2')

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
    plt.savefig(f'SPP_INC_SB_C2/{instance_name}.png')
    plt.close()

def positive_range(end):
    if end < 0:
        return []
    return range(end)

def SPP_Incremental(rectangles, strip_width, lower_bound, upper_bound, timeout=1800):
    """
    Solve 2SPP using incremental SAT solving as described in the paper.
    Returns the optimal height and the positions of rectangles.
    """
    global variables_length, clauses_length
    n_rectangles = len(rectangles)
    
    # Initialize the CNF formula and variables
    cnf = CNF()
    variables = {}
    counter = 1
    
    # Start a timer for the timeout
    start_time = timeit.default_timer()
    
    # Find max height and width for symmetry breaking
    max_height = max([rectangle[1] for rectangle in rectangles])
    max_width = max([rectangle[0] for rectangle in rectangles])
    
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
        for e in positive_range(strip_width - rectangles[i][0] + 2):
            variables[f"px{i+1},{e}"] = counter  # pxi,e
            counter += 1
            
        for f in positive_range(upper_bound - rectangles[i][1] + 2):
            variables[f"py{i+1},{f}"] = counter  # pyi,f
            counter += 1
    
    # Height variables - ph_h means "can pack with height ≤ h"
    for h in range(lower_bound, upper_bound + 1):
        variables[f"ph_{h}"] = counter
        counter += 1
    
    # Add order encoding axiom clauses
    for i in range(n_rectangles):
        # ¬pxi,e ∨ pxi,e+1
        for e in range(strip_width - rectangles[i][0] + 1):
            cnf.append([-variables[f"px{i+1},{e}"], variables[f"px{i+1},{e+1}"]])
        
        # ¬pyi,f ∨ pyi,f+1
        for f in range(upper_bound - rectangles[i][1] + 1):
            cnf.append([-variables[f"py{i+1},{f}"], variables[f"py{i+1},{f+1}"]])
    
    # Add height variable ordering constraints (formula 7 in the paper)
    # If ph_o is true, then ph_{o+1} must also be true
    for h in range(lower_bound, upper_bound):
        cnf.append([-variables[f"ph_{h}"], variables[f"ph_{h+1}"]])
    
    # Define the non-overlapping constraints function
    def add_non_overlapping(i, j, h1, h2, v1, v2):
        i_width = rectangles[i][0]
        i_height = rectangles[i][1]
        j_width = rectangles[j][0]
        j_height = rectangles[j][1]
        
        # lri,j ∨ lrj,i ∨ udi,j ∨ udj,i (formula 4 in the paper)
        four_literal = []
        if h1: four_literal.append(variables[f"lr{i+1},{j+1}"])
        if h2: four_literal.append(variables[f"lr{j+1},{i+1}"])
        if v1: four_literal.append(variables[f"ud{i+1},{j+1}"])
        if v2: four_literal.append(variables[f"ud{j+1},{i+1}"])
        cnf.append(four_literal)
        
        # First type constraints (formula 5 in the paper)
        # ¬lri,j ∨ ¬pxj,e
        if h1:
            for e in range(i_width):
                if f"px{j+1},{e}" in variables:
                    cnf.append([-variables[f"lr{i+1},{j+1}"], -variables[f"px{j+1},{e}"]])
        
        # ¬lrj,i ∨ ¬pxi,e
        if h2:
            for e in range(j_width):
                if f"px{i+1},{e}" in variables:
                    cnf.append([-variables[f"lr{j+1},{i+1}"], -variables[f"px{i+1},{e}"]])
        
        # ¬udi,j ∨ ¬pyj,f
        if v1:
            for f in range(i_height):
                if f"py{j+1},{f}" in variables:
                    cnf.append([-variables[f"ud{i+1},{j+1}"], -variables[f"py{j+1},{f}"]])
        
        # ¬udj,i ∨ ¬pyi,f
        if v2:
            for f in range(j_height):
                if f"py{i+1},{f}" in variables:
                    cnf.append([-variables[f"ud{j+1},{i+1}"], -variables[f"py{i+1},{f}"]])
        
        # Second type constraints (formula 5 continued)
        # ¬lri,j ∨ pxi,e ∨ ¬pxj,e+wi
        if h1:
            for e in positive_range(strip_width - i_width):
                if f"px{j+1},{e+i_width}" in variables:
                    cnf.append([-variables[f"lr{i+1},{j+1}"], 
                              variables[f"px{i+1},{e}"], 
                              -variables[f"px{j+1},{e+i_width}"]])
        
        # ¬lrj,i ∨ pxj,e ∨ ¬pxi,e+wj
        if h2:
            for e in positive_range(strip_width - j_width):
                if f"px{i+1},{e+j_width}" in variables:
                    cnf.append([-variables[f"lr{j+1},{i+1}"], 
                              variables[f"px{j+1},{e}"], 
                              -variables[f"px{i+1},{e+j_width}"]])
        
        # ¬udi,j ∨ pyi,f ∨ ¬pyj,f+hi
        if v1:
            for f in positive_range(upper_bound - i_height):
                if f"py{j+1},{f+i_height}" in variables:
                    cnf.append([-variables[f"ud{i+1},{j+1}"], 
                              variables[f"py{i+1},{f}"], 
                              -variables[f"py{j+1},{f+i_height}"]])
        
        # ¬udj,i ∨ pyj,f ∨ ¬pyi,f+hj
        if v2:
            for f in positive_range(upper_bound - j_height):
                if f"py{i+1},{f+j_height}" in variables:
                    cnf.append([-variables[f"ud{j+1},{i+1}"], 
                              variables[f"py{j+1},{f}"], 
                              -variables[f"py{i+1},{f+j_height}"]])
    
    max_width = max([int(rectangle[0]) for rectangle in rectangles])
    second_max_width = max([int(rectangle[0]) for rectangle in rectangles if int(rectangle[0]) != max_width])

    # Symmetry Breaking - Config 2
    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            #Fix the position of the largest rectangle and the second largest rectangle
            if rectangles[i][0] == max_width and rectangles[j][0] == second_max_width:
                add_non_overlapping(i, j, True, False, True, False)
            # Large-rectangles horizontal
            if rectangles[i][0] + rectangles[j][0] > strip_width:
                add_non_overlapping(i, j, False, False, True, True)
            # Large-rectangles vertical
            elif rectangles[i][1] + rectangles[j][1] > upper_bound:
                add_non_overlapping(i, j, True, True, False, False)
            # Same-sized rectangles
            elif rectangles[i] == rectangles[j]:
                add_non_overlapping(i, j, True, False, True, True)
            else:
                add_non_overlapping(i, j, True, True, True, True)
    
    # Domain encoding (rectangles must stay inside strip)
    for i in range(n_rectangles):
        # px(i, W-wi) - right edge must be inside strip width
        cnf.append([variables[f"px{i+1},{strip_width - rectangles[i][0]}"]])
    
    # Height constraints (formula 6 in paper)
    # For each height h, if ph_h is true, all rectangles must be below h
    for h in range(lower_bound, upper_bound + 1):
        for i in range(n_rectangles):
            # If ph_h is true, rectangle i must have its top edge at or below h
            if h >= rectangles[i][1]:
                cnf.append([-variables[f"ph_{h}"], variables[f"py{i+1},{h - rectangles[i][1]}"]])
    
    # Initialize the incremental SAT solver with the CNF formula
    with Glucose42(bootstrap_with=cnf) as solver:
        optimal_height = upper_bound
        positions = None
        
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
            
            # If we have a previous model, we can use it to help guide the solver
            if best_model is not None:
                # Set phase saving based on previous model (model reuse technique)
                # (Note: Glucose4 in PySAT might not directly support this feature, but the concept is here)
                pass
            
            # Solve with assumptions
            is_sat = solver.solve(assumptions=assumptions)
            
            if is_sat:
                # We found a solution with height ≤ mid
                optimal_height = mid
                
                # Save the model for reuse in future iterations
                best_model = solver.get_model()
                
                # Extract positions from the model
                positions = [[0, 0] for _ in range(n_rectangles)]
                model_vars = {abs(v): v > 0 for v in best_model}
                
                for i in range(n_rectangles):
                    # Find x position (first position where px is true)
                    for e in range(strip_width - rectangles[i][0] + 1):
                        var = variables.get(f"px{i+1},{e}", None)
                        if var is None:
                            continue
                        
                        is_true = model_vars.get(var, False)
                        prev_var = variables.get(f"px{i+1},{e-1}", None)
                        prev_is_true = model_vars.get(prev_var, False) if prev_var is not None else False
                        
                        if is_true and (e == 0 or not prev_is_true):
                            positions[i][0] = e
                            break
                    
                    # Find y position (first position where py is true)
                    for f in range(upper_bound - rectangles[i][1] + 1):
                        var = variables.get(f"py{i+1},{f}", None)
                        if var is None:
                            continue
                        
                        is_true = model_vars.get(var, False)
                        prev_var = variables.get(f"py{i+1},{f-1}", None)
                        prev_is_true = model_vars.get(prev_var, False) if prev_var is not None else False
                        
                        if is_true and (f == 0 or not prev_is_true):
                            positions[i][1] = f
                            break
                
                # Update search range - try lower height
                current_ub = mid - 1
                
                # This is the key part: Add the learned clause permanently
                # (In PySAT we just continue, but the solver keeps the learned clauses)
            
            else:
                # No solution with height ≤ mid
                # Update search range - try higher height
                current_lb = mid + 1

        variables_length = len(variables)
        clauses_length = len(cnf.clauses)

        return optimal_height, positions

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
            upper_bound = min(sum(heights), calculate_first_fit_upper_bound(width, rectangles))
            lower_bound = max(math.ceil(sum([int(rectangle[0] * rectangle[1]) for rectangle in rectangles]) / width), max(heights))

            print(f"Solving 2D Strip Packing with incremental SAT for instance {instance_name}")
            print(f"Width: {width}")
            print(f"Number of rectangles: {n_rec}")
            print(f"Lower bound: {lower_bound}")
            print(f"Upper bound: {upper_bound}")
            
            # Solve with incremental SAT
            optimal_height, optimal_pos = SPP_Incremental(rectangles, width, lower_bound, upper_bound)
            
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
    df.to_excel('SPP_INC_SB_C2.xlsx', index=False)
    print("\nResults saved to SPP_INC_SB_C2.xlsx")

except KeyboardInterrupt:
    print("\nKeyboard interrupt detected. Printing current results:")
    for result in results_data:
        print(result)
    df = pd.DataFrame(results_data)
    df.to_excel('SPP_INC_SB_C2.xlsx', index=False)
    print("\nPartial results saved to SPP_INC_SB_C2.xlsx")
            