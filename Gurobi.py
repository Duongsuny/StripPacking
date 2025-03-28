from gurobipy import Model, GRB, quicksum
import fileinput
import matplotlib.pyplot as plt
import time

def solve_strip_packing(widths, heights, strip_width, time_limit=30, allow_rotation=True):
    # Create model
    mdl = Model("StripPacking")
    mdl.setParam('OutputFlag', 0)  # Suppress Gurobi output (set to 1 for logs)
    mdl.setParam('TimeLimit', time_limit)  # Set time limit in seconds
    
    # Number of rectangles
    n = len(widths)
    
    # Variables
    x = mdl.addVars(n, lb=0, ub=strip_width, vtype=GRB.CONTINUOUS, name="x")  # x-coordinates
    y = mdl.addVars(n, lb=0, vtype=GRB.CONTINUOUS, name="y")  # y-coordinates
    H = mdl.addVar(vtype=GRB.CONTINUOUS, name="H")  # Strip height to minimize
    
    # Rotation variables (optional)
    if allow_rotation:
        rotate = mdl.addVars(n, vtype=GRB.BINARY, name="rotate")  # 1 if rotated, 0 if not
    else:
        rotate = {i: 0 for i in range(n)}  # Fixed orientation
    
    # Non-overlapping variables (left[i,j] = 1 if i is left of j, 0 if above)
    left = mdl.addVars([(i,j) for i in range(n) for j in range(i+1, n)], 
                      vtype=GRB.BINARY, name="left")
    
    # Big-M values
    M_width = strip_width
    M_height = max(max(widths), max(heights)) * n
    
    # Constraints
    for i in range(n):
        # Effective width and height based on rotation
        w_i = mdl.addVar(vtype=GRB.CONTINUOUS, name=f"w_{i}")
        h_i = mdl.addVar(vtype=GRB.CONTINUOUS, name=f"h_{i}")
        if allow_rotation:
            mdl.addConstr(w_i == rotate[i] * heights[i] + (1 - rotate[i]) * widths[i])
            mdl.addConstr(h_i == rotate[i] * widths[i] + (1 - rotate[i]) * heights[i])
        else:
            mdl.addConstr(w_i == widths[i])
            mdl.addConstr(h_i == heights[i])
        
        # Stay within bounds
        mdl.addConstr(x[i] + w_i <= strip_width, f"width_bound_{i}")
        mdl.addConstr(y[i] + h_i <= H, f"height_bound_{i}")
    
    # Non-overlapping constraints
    for i in range(n):
        for j in range(i + 1, n):
            w_i = mdl.getVarByName(f"w_{i}")
            h_i = mdl.getVarByName(f"h_{i}")
            w_j = mdl.getVarByName(f"w_{j}")
            h_j = mdl.getVarByName(f"h_{j}")
            
            # Either i is left of j OR i is above j
            mdl.addConstr(x[i] + w_i <= x[j] + M_width * (1 - left[i,j]), f"left_{i}_{j}")
            mdl.addConstr(y[j] + h_j <= y[i] + M_height * left[i,j], f"above_{i}_{j}")
    
    # Objective: minimize height
    mdl.setObjective(H, GRB.MINIMIZE)
    
    # Optimize
    start_time = time.time()
    mdl.optimize()
    solve_time = time.time() - start_time
    
    if mdl.status == GRB.OPTIMAL or mdl.status == GRB.TIME_LIMIT:
        return {
            'height': H.X,
            'positions': [(x[i].X, y[i].X) for i in range(n)],
            'rotations': [rotate[i].X if allow_rotation else 0 for i in range(n)],
            'objective_value': mdl.ObjVal,
            'solve_time': solve_time,
            'status': 'Optimal' if mdl.status == GRB.OPTIMAL else 'Time Limit'
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
    n_instance = 10
    input_data = read_file_instance(n_instance)
    
    if input_data is None:
        return
    
    strip_width = int(input_data[0])
    n_rec = int(input_data[1])
    rectangles = [[int(val) for val in line.split()] for line in input_data[2:2+n_rec]]
    widths = [rect[0] for rect in rectangles]
    heights = [rect[1] for rect in rectangles]
    
    # Solve with Gurobi
    result = solve_strip_packing(widths, heights, strip_width, time_limit=30, allow_rotation=True)
    
    if result:
        print(f"Strip height: {result['height']:.2f}")
        print(f"Solve time: {result['solve_time']:.2f} seconds")
        print(f"Status: {result['status']}")
        print("Rectangle positions (x, y) and rotation status:")
        for i, (x_pos, y_pos) in enumerate(result['positions']):
            rot_status = "Rotated" if result['rotations'][i] >= 0.5 else "Not Rotated"
            effective_w = heights[i] if result['rotations'][i] >= 0.5 else widths[i]
            effective_h = widths[i] if result['rotations'][i] >= 0.5 else heights[i]
            print(f"Rectangle {i}: ({x_pos:.2f}, {y_pos:.2f}) "
                  f"width={effective_w}, height={effective_h}, {rot_status}")
        
        strip = [strip_width, result['height']]
        display_solution(strip, rectangles, result['positions'], result['rotations'])

if __name__ == "__main__":
    main()