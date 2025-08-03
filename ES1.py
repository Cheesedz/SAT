from itertools import combinations, product
from pysat.formula import CNF
from pysat.solvers import Solver
import time

# Start timer
start_time = time.time()

# -------------------------------
# Problem Parameters (Example)
# -------------------------------
n = 2  # number of tasks
m = 2  # number of resources
T = 5  # total time slots (assuming d_i - r_i = T for simplicity)
e = [2, 2]  # execution time of tasks
r = [0, 0]  # release time
d = [5, 5]  # deadline

# -------------------------------
# Variable ID Mapping
# -------------------------------
var_counter = 1
x = {}  # x[i][j][t] -> var
a = {}  # a[i][j][t] -> var

for i in range(n):
    for j in range(m):
        for t in range(r[i], d[i]):
            x[i, j, t] = var_counter
            var_counter += 1
        for t in range(r[i], d[i] - e[i] + 1):
            a[i, j, t] = var_counter
            var_counter += 1

cnf = CNF()

# -------------------------------
# A1: Task cannot use 2 resources
# -------------------------------
for i in range(n):
    for (j1, j2) in combinations(range(m), 2):
        clause = []
        for t1 in range(r[i], d[i]):
            for t2 in range(r[i], d[i]):
                clause = [-x[i, j1, t1], -x[i, j2, t2]]
                cnf.append(clause)

# -------------------------------
# A2: Each task must use at least one resource
# -------------------------------
for i in range(n):
    clause = []
    for j in range(m):
        for t in range(r[i], d[i]):
            clause.append(x[i, j, t])
    cnf.append(clause)

# -------------------------------
# A3: Resource conflict prevention
# Only one task can access resource j at time t
# -------------------------------
for j in range(m):
    for t in range(T):
        for (i1, i2) in combinations(range(n), 2):
            if (i1, j, t) in x and (i2, j, t) in x:
                cnf.append([-x[i1, j, t], -x[i2, j, t]])

# -------------------------------
# A4: At least one non-preemptive start per task
# -------------------------------
for i in range(n):
    clause = []
    for j in range(m):
        for t in range(r[i], d[i] - e[i] + 1):
            clause.append(a[i, j, t])
    cnf.append(clause)

# -------------------------------
# A5: Encode A_ij^t <-> non-preemptive x variables
# -------------------------------
for i in range(n):
    for j in range(m):
        for t in range(r[i], d[i] - e[i] + 1):
            y_vars = []
            # build list of y_vars = x[i, j, t'] over non-preemptive window
            for t_prime in range(r[i], d[i]):
                if t_prime < t or t_prime >= t + e[i]:
                    y_vars.append(-x[i, j, t_prime])
                else:
                    y_vars.append(x[i, j, t_prime])
            # Add clauses:
            # (¬a OR y1) ∧ ... ∧ (¬a OR yr)
            for y in y_vars:
                cnf.append([-a[i, j, t], y])
            # (¬y1 ∨ ¬y2 ∨ ... ∨ ¬yr ∨ a)
            cnf.append([-y for y in y_vars] + [a[i, j, t]])

# -------------------------------
# SAT Solver
# -------------------------------
with Solver(bootstrap_with=cnf.clauses) as solver:
    satisfiable = solver.solve()
    if satisfiable:
        model = solver.get_model()
        print("SATISFIABLE")
        # Print variable assignments (optional)
        for k, v in x.items():
            if model[v - 1] > 0:
                print(f"x[{k}] = 1")
        for k, v in a.items():
            if model[v - 1] > 0:
                print(f"A[{k}] = 1")
    else:
        print("UNSATISFIABLE")
        
# -------------------------------
# Time Measurement
# -------------------------------
end_time = time.time()
elapsed_time = end_time - start_time
print(f"\n Total solving time: {elapsed_time:.4f} seconds")
print(f"Number of variables: {var_counter}")
print(f"Number of clauses: {len(cnf.clauses)}")

