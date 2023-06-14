# FStar-DPLL-licenta

folder 'bkt' holds the BKT solution for the boolean SAT problem.

folder 'dpll' holds an optimization of the 'bkt' folder solution, where 'unit clause propagation' was added to the solution.

folder 'dpll_optimized' holds an optimized version of 'dpll' folder solution, where the program looks for potential 'false clauses' only in the clauses which have had new a false literal appear at the current step.
