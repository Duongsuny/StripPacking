import time
from ortools.sat.python import cp_model
import matplotlib.pyplot as plt
import fileinput

# Read file
def read_file_instance(n_instance):
    s = ''
    filepath = "inputs/ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

# Display the solution
def display_solution(strip, rectangles, positions):
    fig, ax = plt.subplots()
    ax = plt.gca()
    plt.title(f"Strip packing solution with height {strip[1]}")
    
    if len(positions) > 0:
        for i in range(len(rectangles)):
            rect = plt.Rectangle(positions[i], *rectangles[i], edgecolor="#333")
            ax.add_patch(rect)
    
    ax.set_xlim(0, strip[0])
    ax.set_ylim(0, strip[1] + 1)
    ax.set_xticks(range(strip[0] + 1))
    ax.set_yticks(range(strip[1] + 1))
    ax.set_xlabel('width')
    ax.set_ylabel('height')
    
    plt.savefig(f'height{strip[1]}.png')
    plt.show()

# Read input file
input = read_file_instance(10)  # Change instance number here (from 0 - 40)
width = int(input[0])
n_rec = int(input[1])
rectangles = [[int(val) for val in i.split()] for i in input[-n_rec:]]
print(rectangles)

# Function to pack rectangles into a strip of a given width, minimizing height
def solve_strip_packing(width, rectangles):
    model = cp_model.CpModel()
    
    # Decision variable: height of the strip (to be minimized)
    max_height = sum(rect[1] for rect in rectangles)  # The maximum possible height
    height = model.NewIntVar(0, max_height, 'height')
    
    # Variables: x, y coordinates and rotation for each rectangle
    x = []
    y = []
    rotations = []
    
    for i in range(len(rectangles)):
        # Coordinates
        x.append(model.NewIntVar(0, width - min(rectangles[i][0], rectangles[i][1]), f'x{i}'))
        y.append(model.NewIntVar(0, max_height, f'y{i}'))  # y-coordinates bounded by max possible height
        
        # Rotation (0 = no rotation, 1 = rotated)
        rotations.append(model.NewBoolVar(f'rot{i}'))
    
    # No overlap constraints
    for i in range(len(rectangles)):
        for j in range(i + 1, len(rectangles)):
            # Add constraints depending on whether each rectangle is rotated
            rect_i_w = model.NewIntVar(0, width, f'rect_i_w_{i}')
            rect_i_h = model.NewIntVar(0, max_height, f'rect_i_h_{i}')
            rect_j_w = model.NewIntVar(0, width, f'rect_j_w_{j}')
            rect_j_h = model.NewIntVar(0, max_height, f'rect_j_h_{j}')

            # If not rotated, width and height remain the same; otherwise, they are swapped
            model.Add(rect_i_w == rectangles[i][0]).OnlyEnforceIf(rotations[i].Not())
            model.Add(rect_i_h == rectangles[i][1]).OnlyEnforceIf(rotations[i].Not())
            model.Add(rect_i_w == rectangles[i][1]).OnlyEnforceIf(rotations[i])
            model.Add(rect_i_h == rectangles[i][0]).OnlyEnforceIf(rotations[i])

            model.Add(rect_j_w == rectangles[j][0]).OnlyEnforceIf(rotations[j].Not())
            model.Add(rect_j_h == rectangles[j][1]).OnlyEnforceIf(rotations[j].Not())
            model.Add(rect_j_w == rectangles[j][1]).OnlyEnforceIf(rotations[j])
            model.Add(rect_j_h == rectangles[j][0]).OnlyEnforceIf(rotations[j])

            # Boolean variables to represent the disjunctions (i is left/right/above/below of j)
            left = model.NewBoolVar(f'left_{i}_{j}')
            right = model.NewBoolVar(f'right_{i}_{j}')
            below = model.NewBoolVar(f'below_{i}_{j}')
            above = model.NewBoolVar(f'above_{i}_{j}')
            
            # Add the constraints for these boolean variables
            model.Add(x[i] + rect_i_w <= x[j]).OnlyEnforceIf(left)
            model.Add(x[j] + rect_j_w <= x[i]).OnlyEnforceIf(right)
            model.Add(y[i] + rect_i_h <= y[j]).OnlyEnforceIf(below)
            model.Add(y[j] + rect_j_h <= y[i]).OnlyEnforceIf(above)
            
            # At least one of the constraints must hold (non-overlapping condition)
            model.AddBoolOr([left, right, below, above])

    # Each rectangle must be placed within the strip's height
    for i in range(len(rectangles)):
        rect_w = model.NewIntVar(0, width, f'rect_w_{i}')
        rect_h = model.NewIntVar(0, max_height, f'rect_h_{i}')
        model.Add(rect_w == rectangles[i][0]).OnlyEnforceIf(rotations[i].Not())
        model.Add(rect_h == rectangles[i][1]).OnlyEnforceIf(rotations[i].Not())
        model.Add(rect_w == rectangles[i][1]).OnlyEnforceIf(rotations[i])
        model.Add(rect_h == rectangles[i][0]).OnlyEnforceIf(rotations[i])
        
        # Ensure that the rectangle fits within the strip height
        model.Add(y[i] + rect_h <= height)
    
    # Minimize the height
    model.Minimize(height)
    
    # Solver setup
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60.0
    status = solver.Solve(model)
    
    # If a solution is found, return the coordinates and height of the rectangles
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        positions = [(solver.Value(x[i]), solver.Value(y[i])) for i in range(len(rectangles))]
        rotated_rectangles = [(solver.Value(rotations[i])) for i in range(len(rectangles))]
        final_rectangles = [
            (rectangles[i][1], rectangles[i][0]) if rotated_rectangles[i] else rectangles[i]
            for i in range(len(rectangles))
        ]
        final_height = solver.Value(height)
        return True, final_height, positions, final_rectangles
    else:
        return False, 0, [], []

# Compare runtimes and display the solution
start_solve = time.time()
is_feasible, optimal_height, best_positions, final_rectangles = solve_strip_packing(width, rectangles)
end_solve = time.time()

if is_feasible:
    print(f"Optimal Height = {optimal_height}")
    print(f"Time taken: {end_solve - start_solve} seconds")
    # Display the solution
    display_solution((width, optimal_height), final_rectangles, best_positions)
else:
    print("No solution found.")