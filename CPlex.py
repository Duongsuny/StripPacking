from docplex.mp.model import Model
import fileinput
import matplotlib.pyplot as plt
import pandas as pd
import time

def solve_strip_packing(widths, heights, strip_width):
    # Create model
    mdl = Model("StripPacking")
    
    # Number of rectangles
    n = len(widths)
    
    # Variables
    x = mdl.continuous_var_list(n, lb=0, ub=strip_width, name="x")
    y = mdl.continuous_var_list(n, lb=0, name="y")
    
    # Maximum height (objective to minimize)
    H = mdl.continuous_var(name="H")
    
    # Binary variables for non-overlapping constraints
    lr = mdl.binary_var_matrix(range(n), range(n), name="lr")
    rl = mdl.binary_var_matrix(range(n), range(n), name="rl")
    ab = mdl.binary_var_matrix(range(n), range(n), name="ab")
    ba = mdl.binary_var_matrix(range(n), range(n), name="ba")
    
    # Big M constant
    M = strip_width + max(heights)
    
    # Constraints
    for i in range(n):
        mdl.add_constraint(y[i] + heights[i] <= H)
        mdl.add_constraint(x[i] + widths[i] <= strip_width)
    
    for i in range(n):
        for j in range(i + 1, n):
            mdl.add_constraint(lr[i,j] + rl[i,j] + ab[i,j] + ba[i,j] >= 1)
            mdl.add_constraint(x[i] + widths[i] <= x[j] + M * (1 - lr[i,j]))
            mdl.add_constraint(x[j] + widths[j] <= x[i] + M * (1 - rl[i,j]))
            mdl.add_constraint(y[i] + heights[i] <= y[j] + M * (1 - ab[i,j]))
            mdl.add_constraint(y[j] + heights[j] <= y[i] + M * (1 - ba[i,j]))
    
    # Objective: minimize height
    mdl.minimize(H)
    
    # Solve
    solution = mdl.solve()
    
    if solution:
        return {
            'height': solution[H],
            'positions': [(solution[x[i]], solution[y[i]]) for i in range(n)],
            'objective_value': mdl.objective_value
        }
    else:
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
def display_solution(strip, rectangles, pos_circuits):
    fig, ax = plt.subplots()
    plt.title(f"Strip Packing Solution (Width: {strip[0]}, Height: {strip[1]:.2f})")

    if len(pos_circuits) > 0:
        for i in range(len(rectangles)):
            rect = plt.Rectangle(pos_circuits[i], rectangles[i][0], rectangles[i][1], 
                               edgecolor="#333", facecolor="lightblue", alpha=0.6)
            ax.add_patch(rect)
            # Add rectangle number at center
            rx, ry = pos_circuits[i]
            cx, cy = rx + rectangles[i][0]/2, ry + rectangles[i][1]/2
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
    
    # Run instances 1 through 10
    for n_instance in range(1, 5):
        print(f"\nProcessing instance {n_instance}")
        input_data = read_file_instance(n_instance)
        
        if input_data is None:
            continue
        
        # Parse input
        strip_width = int(input_data[0])
        n_rec = int(input_data[1])
        rectangles = [[int(val) for val in line.split()] for line in input_data[2:2+n_rec]]
        widths = [rect[0] for rect in rectangles]
        heights = [rect[1] for rect in rectangles]
        
        # Solve the problem and measure time
        start_time = time.time()
        result = solve_strip_packing(widths, heights, strip_width)
        solve_time = time.time() - start_time
        
        if result:
            print(f"Instance {n_instance} - Height: {result['height']:.2f}, Time: {solve_time:.2f}s")
            results.append({
                'Instance': n_instance,
                'Optimal_Height': result['height'],
                'Runtime_Seconds': solve_time,
                'Number_of_Rectangles': n_rec,
                'Strip_Width': strip_width
            })
        else:
            print(f"Instance {n_instance} - No solution found")
            
    # Create DataFrame and save to Excel
    df = pd.DataFrame(results)
    excel_file = 'strip_packing_results.xlsx'
    df.to_excel(excel_file, index=False)
    print(f"\nResults saved to {excel_file}")

if __name__ == "__main__":
    main()