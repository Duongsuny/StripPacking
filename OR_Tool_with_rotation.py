from ortools.linear_solver import pywraplp
import matplotlib.pyplot as plt
import fileinput
import pandas as pd
import time

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

def solve_strip_packing(strip_width, items):
    """
    Solves the strip packing problem with rotation option.
    items: List of tuples (width, height) for each rectangle
    strip_width: Fixed width of the strip
    """
    solver = pywraplp.Solver.CreateSolver('SCIP')
    if not solver:
        return None

    # Set time limit to 300 seconds
    solver.SetTimeLimit(300 * 1000)  # Time limit in milliseconds

    n = len(items)
    
    # Calculate bounds for height
    max_single_height = max(max(w, h) for w, h in items)  # Tallest possible rectangle
    total_area = sum(w * h for w, h in items)
    area_bound = total_area / strip_width
    lower_bound = max(max_single_height, area_bound)  # Lower bound on height
    upper_bound = sum(max(w, h) for w, h in items)    # Upper bound on height
    
    # Variables
    x = [solver.NumVar(0, strip_width, f'x_{i}') for i in range(n)]
    y = [solver.NumVar(0, upper_bound, f'y_{i}') for i in range(n)]  # Use upper_bound as max y
    rotate = [solver.BoolVar(f'rotate_{i}') for i in range(n)]  # 1 if rotated, 0 if not
    
    # Binary variables for relative positions
    left = [[solver.BoolVar(f'left_{i}_{j}') for j in range(n)] 
            for i in range(n)]
    below = [[solver.BoolVar(f'below_{i}_{j}') for j in range(n)] 
             for i in range(n)]
    
    height = solver.NumVar(lower_bound, upper_bound, 'height')  # Height with bounds

    # Constraints
    for i in range(n):
        w, h = items[i]
        # Width constraint considering rotation
        solver.Add(x[i] + w * (1 - rotate[i]) + h * rotate[i] <= strip_width)
        # Height constraint considering rotation
        solver.Add(y[i] + h * (1 - rotate[i]) + w * rotate[i] <= height)
        
        for j in range(i + 1, n):
            wj, hj = items[j]
            M = strip_width + upper_bound  # Updated M with upper_bound
            
            # Left constraint considering rotations
            solver.Add(x[i] + 
                      w * (1 - rotate[i]) + h * rotate[i] <= 
                      x[j] + M * (1 - left[i][j]))
            solver.Add(x[j] + 
                      wj * (1 - rotate[j]) + hj * rotate[j] <= 
                      x[i] + M * (1 - left[j][i]))
            
            # Below constraint considering rotations
            solver.Add(y[i] + 
                      h * (1 - rotate[i]) + w * rotate[i] <= 
                      y[j] + M * (1 - below[i][j]))
            solver.Add(y[j] + 
                      hj * (1 - rotate[j]) + wj * rotate[j] <= 
                      y[i] + M * (1 - below[j][i]))
            
            # At least one condition must hold
            solver.Add(left[i][j] + left[j][i] + below[i][j] + below[j][i] >= 1)

    # Objective: minimize height
    solver.Minimize(height)

    # Solve
    status = solver.Solve()
    
    if status == pywraplp.Solver.OPTIMAL:
        solution = {
            'height': solver.Objective().Value(),
            'positions': [(x[i].solution_value(), y[i].solution_value()) 
                         for i in range(n)],
            'rotations': [rotate[i].solution_value() for i in range(n)],
            'lower_bound': lower_bound,
            'upper_bound': upper_bound,
            'runtime': solver.WallTime() / 1000.0  # Convert to seconds
        }
        return solution
    else:
        print(f"No optimal solution found. Status: {status}")
        return None

def visualize_solution(strip_width, items, solution):
    """Visualize the packing solution with rotations"""
    fig, ax = plt.subplots()
    
    for i, (pos_x, pos_y) in enumerate(solution['positions']):
        w, h = items[i]
        # Apply rotation
        width = h if solution["rotations"][i] > 0.5 else w
        height = w if solution["rotations"][i] > 0.5 else h
        rect = plt.Rectangle((pos_x, pos_y), width, height,
                           edgecolor='black', facecolor='skyblue', alpha=0.6)
        ax.add_patch(rect)
        
        # Add label with rotation info
        label = f'Item {i}\n{"R" if solution["rotations"][i] > 0.5 else "NR"}'
        ax.text(pos_x + width/2, pos_y + height/2, label,
                ha='center', va='center')
    
    ax.set_xlim(0, strip_width)
    ax.set_ylim(0, solution['height'] * 1.1)
    ax.set_xlabel('Width')
    ax.set_ylabel('Height')
    ax.set_title(f'Strip Packing Solution (Height: {solution["height"]:.2f})')
    plt.grid(True)
    plt.show()

def main():
    results = []
    
    for instance in get_instances_from_c(start_level=1, end_level=2):  # 0 to 30
        print(f"\nSolving instance {instance}...")
        try:
            input_data = read_file_instance(instance)
            strip_width = int(input_data[0])
            n_rectangles = int(input_data[1])
            items = [[int(val) for val in line.split()] for line in input_data[-n_rectangles:]]
            
            solution = solve_strip_packing(strip_width, items)
            
            if solution:
                results.append({
                    'Instance': instance,
                    'Height': solution['height'],
                    'Runtime': solution['runtime'],
                    'Status': 'Optimal'
                })
                print(f"Instance {instance}: Height = {solution['height']:.2f}, Time = {solution['runtime']:.2f}s")
            else:
                results.append({
                    'Instance': instance,
                    'Height': None,
                    'Runtime': 300,  # Timeout duration
                    'Status': 'Timeout/Infeasible'
                })
                print(f"Instance {instance}: Failed to find solution")
                
        except Exception as e:
            print(f"Error processing instance {instance}: {str(e)}")
            results.append({
                'Instance': instance,
                'Height': None,
                'Runtime': None,
                'Status': 'Error'
            })
    
    # Save results to Excel
    df = pd.DataFrame(results)
    df.to_excel('strip_packing_results_OR_tool.xlsx', index=False)
    print("\nResults saved to strip_packing_results.xlsx")

if __name__ == "__main__":
    main()