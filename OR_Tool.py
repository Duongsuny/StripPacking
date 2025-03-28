from ortools.linear_solver import pywraplp
import matplotlib.pyplot as plt
import fileinput

def read_file_instance(n_instance):
    """Read problem instance from file."""
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

def solve_strip_packing(strip_width, items):
    """
    Solves the strip packing problem.
    items: List of tuples (width, height) for each rectangle
    strip_width: Fixed width of the strip
    """
    # Create the solver
    solver = pywraplp.Solver.CreateSolver('SCIP')
    if not solver:
        return None

    n = len(items)
    # Maximum possible height (sum of all heights as upper bound)
    max_height = sum(item[1] for item in items)
    
    # Variables
    x = [solver.NumVar(0, strip_width, f'x_{i}') for i in range(n)]
    y = [solver.NumVar(0, max_height, f'y_{i}') for i in range(n)]
    
    # Binary variables for relative positions
    left = [[solver.BoolVar(f'left_{i}_{j}') for j in range(n)] 
            for i in range(n)]
    below = [[solver.BoolVar(f'below_{i}_{j}') for j in range(n)] 
             for i in range(n)]
    
    # Height to minimize
    height = solver.NumVar(0, max_height, 'height')

    # Constraints
    for i in range(n):
        # Stay within strip width
        solver.Add(x[i] + items[i][0] <= strip_width)
        # Each item's top must be <= total height
        solver.Add(y[i] + items[i][1] <= height)
        
        for j in range(i + 1, n):
            # Non-overlapping constraints using Big-M
            M = strip_width + max_height
            
            # left[i][j] = 1 if i is left of j
            solver.Add(x[i] + items[i][0] <= x[j] + M * (1 - left[i][j]))
            # left[j][i] = 1 if j is left of i
            solver.Add(x[j] + items[j][0] <= x[i] + M * (1 - left[j][i]))
            # below[i][j] = 1 if i is below j
            solver.Add(y[i] + items[i][1] <= y[j] + M * (1 - below[i][j]))
            # below[j][i] = 1 if j is below i
            solver.Add(y[j] + items[j][1] <= y[i] + M * (1 - below[j][i]))
            
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
                         for i in range(n)]
        }
        return solution
    else:
        print("No optimal solution found")
        return None

def visualize_solution(strip_width, items, solution):
    """Visualize the packing solution"""
    fig, ax = plt.subplots()
    
    for i, (pos_x, pos_y) in enumerate(solution['positions']):
        width, height = items[i]
        rect = plt.Rectangle((pos_x, pos_y), width, height, 
                           edgecolor='black', facecolor='skyblue', alpha=0.6)
        ax.add_patch(rect)
        
        # Add label
        ax.text(pos_x + width/2, pos_y + height/2, f'Item {i}',
                ha='center', va='center')
    
    ax.set_xlim(0, strip_width)
    ax.set_ylim(0, solution['height'] * 1.1)
    ax.set_xlabel('Width')
    ax.set_ylabel('Height')
    ax.set_title(f'Strip Packing Solution (Height: {solution["height"]:.2f})')
    plt.grid(True)
    plt.show()

def main():
    # Read file input
    input_data = read_file_instance(10) # Change instance number (0-40) here
    strip_width = int(input_data[0])
    n_rectangles = int(input_data[1])
    items = [[int(val) for val in line.split()] for line in input_data[-n_rectangles:]]
    
    print("Solving strip packing problem...")
    solution = solve_strip_packing(strip_width, items)
    
    if solution:
        print(f"Optimal height: {solution['height']:.2f}")
        for i, (x_pos, y_pos) in enumerate(solution['positions']):
            print(f"Item {i}: x={x_pos:.2f}, y={y_pos:.2f}")
        
        # Visualize the solution
        visualize_solution(strip_width, items, solution)

if __name__ == "__main__":
    main()