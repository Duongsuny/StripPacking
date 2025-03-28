from docplex.mp.model import Model
import fileinput
import matplotlib.pyplot as plt
import time
import pandas as pd

def solve_strip_packing(widths, heights, strip_width, time_limit=300):
    # Create model
    mdl = Model("StripPacking")
    
    # Performance tuning
    mdl.parameters.timelimit = time_limit  # Set a time limit in seconds
    mdl.parameters.mip.tolerances.mipgap = 0.01  # 1% relative gap
    mdl.parameters.mip.tolerances.absmipgap = 0.01  # 0.01 absolute gap
    
    # Number of rectangles
    n = len(widths)
    
    # Variables
    x = mdl.continuous_var_list(n, lb=0, ub=strip_width, name="x")
    y = mdl.continuous_var_list(n, lb=0, name="y")
    H = mdl.continuous_var(name="H")
    rotate = mdl.binary_var_list(n, name="rotate")
    
    # Binary variables for non-overlapping constraints
    lr = mdl.binary_var_matrix(range(n), range(n), name="lr")
    rl = mdl.binary_var_matrix(range(n), range(n), name="rl")
    ab = mdl.binary_var_matrix(range(n), range(n), name="ab")
    ba = mdl.binary_var_matrix(range(n), range(n), name="ba")
    
    # Big M constant
    M = strip_width + max(max(widths), max(heights))
    
    # Constraints
    for i in range(n):
        w_i = rotate[i] * heights[i] + (1 - rotate[i]) * widths[i]
        h_i = rotate[i] * widths[i] + (1 - rotate[i]) * heights[i]
        mdl.add_constraint(y[i] + h_i <= H)
        mdl.add_constraint(x[i] + w_i <= strip_width)
    
    for i in range(n):
        for j in range(i + 1, n):
            w_i = rotate[i] * heights[i] + (1 - rotate[i]) * widths[i]
            h_i = rotate[i] * widths[i] + (1 - rotate[i]) * heights[i]
            w_j = rotate[j] * heights[j] + (1 - rotate[j]) * widths[j]
            h_j = rotate[j] * widths[j] + (1 - rotate[j]) * heights[j]
            
            mdl.add_constraint(lr[i,j] + rl[i,j] + ab[i,j] + ba[i,j] >= 1)
            mdl.add_constraint(x[i] + w_i <= x[j] + M * (1 - lr[i,j]))
            mdl.add_constraint(x[j] + w_j <= x[i] + M * (1 - rl[i,j]))
            mdl.add_constraint(y[i] + h_i <= y[j] + M * (1 - ab[i,j]))
            mdl.add_constraint(y[j] + h_j <= y[i] + M * (1 - ba[i,j]))
    
    # Objective: minimize height
    mdl.minimize(H)
    
    # Solve and measure time
    start_time = time.time()
    solution = mdl.solve(log_output=False)  # Set to True for solver logs
    solve_time = time.time() - start_time
    
    if solution:
        return {
            'height': solution[H],
            'positions': [(solution[x[i]], solution[y[i]]) for i in range(n)],
            'rotations': [solution[rotate[i]] for i in range(n)],
            'objective_value': mdl.objective_value,
            'solve_time': solve_time
        }
    else:
        print(f"No solution found within {time_limit} seconds")
        return None

# Read file function
def read_file_instance(n_instance):
    s = ''
    filepath = f"inputs/ins-{n_instance}.txt"
    try:
        with open(filepath, 'r') as file:
            s = file.read()
        return s.splitlines()
    except FileNotFoundError:
        print(f"Error: File inputs/ins-{n_instance}.txt not found")
        return None

# Display solution function
def display_solution(strip, rectangles, pos_circuits, rotations):
    fig, ax = plt.subplots()
    plt.title(f"Strip Packing Solution (Width: {strip[0]}, Height: {strip[1]:.2f})")

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
    plt.show()

def main():
    results = []
    time_limit = 300  # 300 seconds timeout
    
    for n_instance in [33, 38, 40]:  # Run instances 31 to 40
        try:
            print(f"\nProcessing instance {n_instance}")
            input_data = read_file_instance(n_instance)
            
            if input_data is None:
                results.append({
                    'Instance': n_instance,
                    'Height': None,
                    'Runtime': None,
                    'Status': 'File Error'
                })
                continue
            
            strip_width = int(input_data[0])
            n_rec = int(input_data[1])
            rectangles = [[int(val) for val in line.split()] for line in input_data[2:2+n_rec]]
            widths = [rect[0] for rect in rectangles]
            heights = [rect[1] for rect in rectangles]
            
            # Solve the problem
            result = solve_strip_packing(widths, heights, strip_width, time_limit=time_limit)
            
            # Store results
            if result:
                results.append({
                    'Instance': n_instance,
                    'Height': result['height'],
                    'Runtime': result['solve_time'],
                    'Status': 'Solved'
                })
                print(f"Instance {n_instance} - Height: {result['height']:.2f}, Time: {result['solve_time']:.2f}s")
            else:
                results.append({
                    'Instance': n_instance,
                    'Height': None,
                    'Runtime': time_limit,
                    'Status': 'Timeout'
                })
                print(f"Instance {n_instance} - Timeout")
                
        except Exception as e:
            print(f"Error processing instance {n_instance}: {str(e)}")
            results.append({
                'Instance': n_instance,
                'Height': None,
                'Runtime': None,
                'Status': f'Error: {str(e)}'
            })
            continue
    
    # Create DataFrame and save to Excel
    df = pd.DataFrame(results)
    df.to_excel('strip_packing_results_cplex.xlsx', index=False)
    print("\nResults saved to strip_packing_results.xlsx")

if __name__ == "__main__":
    main()