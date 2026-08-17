import random
from typing import List, Tuple, Optional


class ConformalLagrangianSATSolver:
    """Deterministic Discrete Lagrangian Gauge Solver for strict 3-SAT."""

    def __init__(
        self,
        num_vars: int,
        clauses: List[List[int]],
        max_flips: int = 25000,
        gauge_step: int = 1,
    ):
        if not isinstance(num_vars, int) or isinstance(num_vars, bool):
            raise TypeError("num_vars must be an integer.")
        if num_vars < 1:
            raise ValueError("num_vars must be >= 1.")
        if not isinstance(max_flips, int) or isinstance(max_flips, bool):
            raise TypeError("max_flips must be an integer.")
        if max_flips < 0:
            raise ValueError("max_flips must be >= 0.")
        if not isinstance(gauge_step, int) or isinstance(gauge_step, bool):
            raise TypeError("gauge_step must be an integer.")
        if gauge_step < 1:
            raise ValueError("gauge_step must be >= 1.")
        if not isinstance(clauses, list):
            raise TypeError("clauses must be a list.")

        self.n = num_vars
        self.clauses = clauses
        self.m = len(clauses)
        self.max_flips = max_flips
        self.gauge_step = gauge_step

        for c_idx, clause in enumerate(self.clauses):
            if not isinstance(clause, list):
                raise TypeError(f"Clause {c_idx} must be a list.")
            if len(clause) != 3:
                raise ValueError(
                    f"Clause {c_idx} must contain exactly 3 literals."
                )
            variables = set()
            for lit in clause:
                if not isinstance(lit, int) or isinstance(lit, bool):
                    raise TypeError(
                        f"Literal {lit!r} in clause {c_idx} must be an integer."
                    )
                if lit == 0:
                    raise ValueError(f"Literal 0 is invalid in clause {c_idx}.")
                v = abs(lit) - 1
                if not (0 <= v < self.n):
                    raise ValueError(
                        f"Literal {lit} in clause {c_idx} is outside the variable range."
                    )
                if v in variables:
                    raise ValueError(
                        f"Clause {c_idx} contains a repeated variable: {abs(lit)}."
                    )
                variables.add(v)

        self.var_to_clauses = [set() for _ in range(self.n)]
        for c_idx, clause in enumerate(self.clauses):
            for lit in clause:
                v = abs(lit) - 1
                self.var_to_clauses[v].add(c_idx)

    @staticmethod
    def literal_satisfied(lit: int, assignment: List[int]) -> bool:
        v = abs(lit) - 1
        if lit > 0:
            return assignment[v] == 1
        return assignment[v] == 0

    def clause_sat_count(self, c_idx: int, assignment: List[int]) -> int:
        return sum(
            self.literal_satisfied(lit, assignment)
            for lit in self.clauses[c_idx]
        )

    def initialize_state(
        self, assignment: List[int]
    ) -> Tuple[List[int], List[int], set, int]:
        sat_count = [
            self.clause_sat_count(c_idx, assignment)
            for c_idx in range(self.m)
        ]
        unsat_clauses = {
            c_idx for c_idx in range(self.m) if sat_count[c_idx] == 0
        }
        lambdas = [1] * self.m
        weighted_cost = sum(lambdas[c_idx] for c_idx in unsat_clauses)
        return sat_count, lambdas, unsat_clauses, weighted_cost

    def hypothetical_flip_delta(
        self,
        v: int,
        assignment: List[int],
        sat_count: List[int],
        lambdas: List[int],
    ) -> int:
        old_value = assignment[v]
        new_value = 1 - old_value
        delta = 0
        for c_idx in self.var_to_clauses[v]:
            old_broken = sat_count[c_idx] == 0
            new_sat_count = 0
            for lit in self.clauses[c_idx]:
                var = abs(lit) - 1
                value = new_value if var == v else assignment[var]
                satisfied = value == 1 if lit > 0 else value == 0
                if satisfied:
                    new_sat_count += 1
            new_broken = new_sat_count == 0
            if old_broken and not new_broken:
                delta -= lambdas[c_idx]
            elif not old_broken and new_broken:
                delta += lambdas[c_idx]
        return delta

    def apply_flip(
        self,
        v: int,
        assignment: List[int],
        sat_count: List[int],
        unsat_clauses: set,
    ) -> None:
        assignment[v] ^= 1
        for c_idx in self.var_to_clauses[v]:
            old_sat = sat_count[c_idx]
            new_sat = self.clause_sat_count(c_idx, assignment)
            sat_count[c_idx] = new_sat
            if old_sat == 0 and new_sat > 0:
                unsat_clauses.discard(c_idx)
            elif old_sat > 0 and new_sat == 0:
                unsat_clauses.add(c_idx)

    def verify_solution(self, assignment: Optional[List[int]]) -> bool:
        if assignment is None:
            return False
        if len(assignment) != self.n:
            return False
        # Require exact Python integers: reject bool, float and int subclasses.
        if any(
            type(value) is not int or value not in (0, 1)
            for value in assignment
        ):
            return False
        for c_idx in range(self.m):
            if self.clause_sat_count(c_idx, assignment) == 0:
                return False
        return True

    def solve(self) -> Optional[List[int]]:
        assignment = [0] * self.n
        sat_count, lambdas, unsat_clauses, weighted_cost = self.initialize_state(
            assignment
        )

        for _step in range(self.max_flips):
            if not unsat_clauses:
                return assignment.copy()

            target_clause_idx = min(unsat_clauses)
            target_clause = self.clauses[target_clause_idx]
            candidate_vars = sorted(abs(lit) - 1 for lit in target_clause)
            best_var = None
            best_cost = float("inf")

            for v in candidate_vars:
                delta = self.hypothetical_flip_delta(
                    v=v,
                    assignment=assignment,
                    sat_count=sat_count,
                    lambdas=lambdas,
                )
                candidate_cost = weighted_cost + delta
                if candidate_cost < best_cost or (
                    candidate_cost == best_cost
                    and (best_var is None or v < best_var)
                ):
                    best_cost = candidate_cost
                    best_var = v

            if best_var is None:
                return None

            self.apply_flip(
                v=best_var,
                assignment=assignment,
                sat_count=sat_count,
                unsat_clauses=unsat_clauses,
            )
            weighted_cost = best_cost

            if unsat_clauses:
                number_unsatisfied = len(unsat_clauses)
                for c_idx in unsat_clauses:
                    lambdas[c_idx] += self.gauge_step
                weighted_cost += self.gauge_step * number_unsatisfied

        if self.verify_solution(assignment):
            return assignment.copy()
        return None


def generate_satisfiable_bench(
    n_vars: int,
    n_clauses: int,
    seed: int = 42,
) -> Tuple[int, List[List[int]], List[int]]:
    if not isinstance(n_vars, int) or isinstance(n_vars, bool):
        raise TypeError("n_vars must be an integer, not bool.")
    if n_vars < 3:
        raise ValueError("3-SAT requires at least 3 variables.")
    if not isinstance(n_clauses, int) or isinstance(n_clauses, bool):
        raise TypeError("n_clauses must be an integer, not bool.")
    if n_clauses < 0:
        raise ValueError("n_clauses must be >= 0.")

    rng = random.Random(seed)
    planted_solution = [rng.choice([0, 1]) for _ in range(n_vars)]
    clauses: List[List[int]] = []

    while len(clauses) < n_clauses:
        vars_chosen = rng.sample(range(1, n_vars + 1), 3)
        clause = []
        for v in vars_chosen:
            is_positive = rng.random() > 0.5
            clause.append(v if is_positive else -v)
        clause_satisfied = any(
            (lit > 0 and planted_solution[abs(lit) - 1] == 1)
            or (lit < 0 and planted_solution[abs(lit) - 1] == 0)
            for lit in clause
        )
        if clause_satisfied:
            clauses.append(clause)

    return n_vars, clauses, planted_solution


if __name__ == "__main__":
    num_vars = 6
    clauses = [
        [1, 2, 3],
        [-1, -2, 4],
        [2, -3, 5],
        [-4, 5, 6],
        [-1, 3, -6],
        [-2, -5, 6],
        [1, -4, -5],
        [3, 4, -6],
    ]
    solver = ConformalLagrangianSATSolver(num_vars, clauses)
    sol = solver.solve()
    print(f"Base Result: {sol} | Validated: {solver.verify_solution(sol)}")

    bench_vars, bench_clauses, _ = generate_satisfiable_bench(20, 80, seed=2026)
    bench_solver = ConformalLagrangianSATSolver(
        bench_vars, bench_clauses, max_flips=10000, gauge_step=1
    )
    bench_sol = bench_solver.solve()
    print(
        f"Dense Result: {bench_sol} | "
        f"Validated: {bench_solver.verify_solution(bench_sol)}"
    )
