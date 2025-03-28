from gurobipy import Model, GRB, quicksum
import fileinput
import matplotlib.pyplot as plt
import time
import pandas as pd

def solve_strip_packing(widths, heights, strip_width, time_limit=300, allow_rotation=True):
    # Create model
    mdl = Model("StripPacking")
    mdl.setParam('OutputFlag', 0)  # Suppress output (set to 1 for logs)
    mdl.setParam('TimeLimit', time_limit)
    mdl.setParam('MIPGap', 0.001)  # 0.1% relative gap
    mdl.setParam('MIPGapAbs', 0.01)  # 0.01 absolute gap
    
    # Number of rectangles
    n = len(widths)
    
    # Calculate bounds for H
    max_single_height = max(max(widths[i], heights[i]) for i in range(n))
    total_area = sum(widths[i] * heights[i] for i in range(n))
    area_bound = total_area / strip_width
    lower_bound = max(max_single_height, area_bound)
    upper_bound = sum(max(widths[i], heights[i]) for i in range(n))
    
    # Variables
    x = mdl.addVars(n, lb=0, ub=strip_width, vtype=GRB.CONTINUOUS, name="x")
    y = mdl.addVars(n, lb=0, vtype=GRB.CONTINUOUS, name="y")
    H = mdl.addVar(lb=lower_bound, ub=upper_bound, vtype=GRB.CONTINUOUS, name="H")
    
    # Rotation variables
    if allow_rotation:
        rotate = mdl.addVars(n, vtype=GRB.BINARY, name="rotate")
    else:
        rotate = {i: 0 for i in range(n)}
    
    # Non-overlapping variables
    lr = mdl.addVars([(i,j) for i in range(n) for j in range(i+1, n)], vtype=GRB.BINARY, name="lr")
    rl = mdl.addVars([(i,j) for i in range(n) for j in range(i+1, n)], vtype=GRB.BINARY, name="rl")
    ab = mdl.addVars([(i,j) for i in range(n) for j in range(i+1, n)], vtype=GRB.BINARY, name="ab")
    ba = mdl.addVars([(i,j) for i in range(n) for j in range(i+1, n)], vtype=GRB.BINARY, name="ba")
    
    # Big-M values
    M_width = strip_width
    M_height = upper_bound
    
    # Effective width and height variables
    w = mdl.addVars(n, vtype=GRB.CONTINUOUS, name="w")
    h = mdl.addVars(n, vtype=GRB.CONTINUOUS, name="h")
    
    # Constraints
    for i in range(n):
        if allow_rotation:
            mdl.addConstr(w[i] == rotate[i] * heights[i] + (1 - rotate[i]) * widths[i], f"w_def_{i}")
            mdl.addConstr(h[i] == rotate[i] * widths[i] + (1 - rotate[i]) * heights[i], f"h_def_{i}")
        else:
            mdl.addConstr(w[i] == widths[i], f"w_def_{i}")
            mdl.addConstr(h[i] == heights[i], f"h_def_{i}")
        
        mdl.addConstr(x[i] + w[i] <= strip_width, f"width_bound_{i}")
        mdl.addConstr(y[i] + h[i] <= H, f"height_bound_{i}")
    
    # Non-overlapping constraints
    for i in range(n):
        for j in range(i + 1, n):
            mdl.addConstr(lr[i,j] + rl[i,j] + ab[i,j] + ba[i,j] >= 1, f"disjunction_{i}_{j}")
            mdl.addConstr(x[i] + w[i] <= x[j] + M_width * (1 - lr[i,j]), f"left_{i}_{j}")
            mdl.addConstr(x[j] + w[j] <= x[i] + M_width * (1 - rl[i,j]), f"right_{i}_{j}")
            mdl.addConstr(y[i] + h[i] <= y[j] + M_height * (1 - ab[i,j]), f"above_{i}_{j}")
            mdl.addConstr(y[j] + h[j] <= y[i] + M_height * (1 - ba[i,j]), f"below_{i}_{j}")
    
    # Objective: minimize height
    mdl.setObjective(H, GRB.MINIMIZE)
    
    # Optimize
    start_time = time.time()
    mdl.optimize()  # No callback, rely on bounds and tolerances
    solve_time = time.time() - start_time
    
    if mdl.status == GRB.OPTIMAL or mdl.status == GRB.TIME_LIMIT:
        return {
            'height': H.X,
            'positions': [(x[i].X, y[i].X) for i in range(n)],
            'rotations': [rotate[i].X if allow_rotation else 0 for i in range(n)],
            'objective_value': mdl.ObjVal,
            'solve_time': solve_time,
            'status': 'Optimal' if mdl.status == GRB.OPTIMAL else 'Time Limit',
            'lower_bound': lower_bound,
            'upper_bound': upper_bound
        }
    else:
        print(f"No feasible solution found. Status: {mdl.status}")
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
            w = rectangles[i][1] if rotations[i] >= 0.5 else rectangles[i][0]
            h = rectangles[i][0] if rotations[i] >= 0.5 else rectangles[i][1]
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
    # Create a list to store results
    results = []
    
    # Run instances 1 through 30
    for n_instance in [33, 38, 40]:
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
        
        try:
            strip_width = int(input_data[0])
            n_rec = int(input_data[1])
            rectangles = [[int(val) for val in line.split()] for line in input_data[2:2+n_rec]]
            widths = [rect[0] for rect in rectangles]
            heights = [rect[1] for rect in rectangles]
            
            # Solve with Gurobi
            result = solve_strip_packing(widths, heights, strip_width, time_limit=300, allow_rotation=True)
            
            if result:
                results.append({
                    'Instance': n_instance,
                    'Height': result['height'],
                    'Runtime': result['solve_time'],
                    'Status': result['status']
                })
                print(f"Instance {n_instance} completed - Height: {result['height']:.2f}, "
                      f"Time: {result['solve_time']:.2f}s, Status: {result['status']}")
            else:
                results.append({
                    'Instance': n_instance,
                    'Height': None,
                    'Runtime': None,
                    'Status': 'No Solution'
                })
                
        except Exception as e:
            results.append({
                'Instance': n_instance,
                'Height': None,
                'Runtime': None,
                'Status': f'Error: {str(e)}'
            })
            print(f"Error processing instance {n_instance}: {str(e)}")
    
    # Convert results to DataFrame and save to Excel
    df = pd.DataFrame(results)
    df.to_excel('strip_packing_results_gurobi.xlsx', index=False)
    print("\nResults saved to strip_packing_results.xlsx")

if __name__ == "__main__":
    main()