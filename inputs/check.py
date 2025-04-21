# inputs/check.py

import fileinput

def read_file_instance(n_instance):
    s = ''
    filepath = "ins-{}.txt".format(n_instance)
    for line in fileinput.input(files=filepath):
        s += line
    return s.splitlines()

# Check from instance 1 to 38
for i in range(1, 39):
    lines = read_file_instance(i)

    # Extract width and number of rectangles
    width = int(lines[0].strip())
    n = int(lines[1].strip())

    # Extract rectangle dimensions
    rectangles = [tuple(map(int, line.strip().split())) for line in lines[2:2+n]]

    # Check if the number of rectangles is exactly n
    contains_exactly_n = len(rectangles) == n

    # Print the results
    print(f"Instance {i}:")
    print(f"Number n: {n}")
    print(f"Width: {width}")
    print(f"Contains exactly n rectangles: {contains_exactly_n}")
    print()  # Print a newline for better readability