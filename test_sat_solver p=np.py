import itertools
import random
import unittest

from sat_solver import (
    ConformalLagrangianSATSolver,
    generate_satisfiable_bench,
)


BASE_CLAUSES = [
    [1, 2, 3],
    [-1, -2, 4],
    [2, -3, 5],
    [-4, 5, 6],
    [-1, 3, -6],
    [-2, -5, 6],
    [1, -4, -5],
    [3, 4, -6],
]


def brute_force_solution(n, clauses):
    """Tiny reference solver used only by tests."""
    for bits in itertools.product((0, 1), repeat=n):
        if all(
            any(
                (bits[abs(lit) - 1] == 1)
                if lit > 0
                else (bits[abs(lit) - 1] == 0)
                for lit in clause
            )
            for clause in clauses
        ):
            return list(bits)
    return None


def explicit_weighted_cost(solver, assignment, lambdas):
    return sum(
        lambdas[c_idx]
        for c_idx in range(solver.m)
        if solver.clause_sat_count(c_idx, assignment) == 0
    )


class TestValidationAndPrimitives(unittest.TestCase):
    def test_rejects_non_3_literal_clauses(self):
        with self.assertRaises(ValueError):
            ConformalLagrangianSATSolver(3, [[1, 2]])
        with self.assertRaises(ValueError):
            ConformalLagrangianSATSolver(4, [[1, 2, 3, 4]])

    def test_rejects_out_of_range_and_zero_literals(self):
        for clause in ([0, 1, 2], [1, 2, 4], [-4, 1, 2]):
            with self.subTest(clause=clause):
                with self.assertRaises(ValueError):
                    ConformalLagrangianSATSolver(3, [list(clause)])

    def test_literal_semantics_and_clause_count(self):
        solver = ConformalLagrangianSATSolver(3, [[1, -2, 3]])
        self.assertTrue(solver.literal_satisfied(1, [1, 1, 0]))
        self.assertFalse(solver.literal_satisfied(-2, [1, 1, 0]))
        self.assertEqual(solver.clause_sat_count(0, [1, 1, 0]), 1)
        self.assertEqual(solver.clause_sat_count(0, [1, 0, 1]), 3)

    def test_initialize_state(self):
        clauses = [[1, 2, 3], [-1, -2, -3], [1, -2, 3]]
        solver = ConformalLagrangianSATSolver(3, clauses)
        sat_count, lambdas, unsat, weighted_cost = solver.initialize_state(
            [0, 0, 0]
        )
        self.assertEqual(sat_count, [0, 3, 1])
        self.assertEqual(lambdas, [1, 1, 1])
        self.assertEqual(unsat, {0})
        self.assertEqual(weighted_cost, 1)

    def test_verify_rejects_none_and_wrong_length(self):
        solver = ConformalLagrangianSATSolver(3, [[1, 2, 3]])
        self.assertFalse(solver.verify_solution(None))
        self.assertFalse(solver.verify_solution([1, 0]))
        self.assertFalse(solver.verify_solution([1, 0, 0, 0]))

    def test_verify_requires_exact_zero_or_one_integers(self):
        solver = ConformalLagrangianSATSolver(3, [[1, 2, 3]])

        # Valid exact integers remain accepted.
        self.assertTrue(solver.verify_solution([1, 0, 0]))

        # Integers outside the Boolean domain are rejected.
        self.assertFalse(solver.verify_solution([1, 0, 7]))
        self.assertFalse(solver.verify_solution([-1, 0, 1]))
        self.assertFalse(solver.verify_solution([2, 0, 1]))

        # Numerically equivalent floats and bools are also rejected.
        self.assertFalse(solver.verify_solution([1.0, 0, 0]))
        self.assertFalse(solver.verify_solution([1, 0.0, 0]))
        self.assertFalse(solver.verify_solution([True, 0, 0]))
        self.assertFalse(solver.verify_solution([1, False, 0]))

    def test_rejects_repeated_variables_in_strict_clauses(self):
        for clause in ([1, 1, 2], [1, -1, 2], [-3, 3, 1]):
            with self.subTest(clause=clause):
                with self.assertRaises(ValueError):
                    ConformalLagrangianSATSolver(3, [list(clause)])

    def test_constructor_parameter_validation(self):
        type_cases = [
            ({"num_vars": 3.0, "clauses": []}, TypeError),
            ({"num_vars": True, "clauses": []}, TypeError),
            ({"num_vars": 3, "clauses": (),}, TypeError),
            ({"num_vars": 3, "clauses": [], "max_flips": 1.5}, TypeError),
            ({"num_vars": 3, "clauses": [], "max_flips": False}, TypeError),
            ({"num_vars": 3, "clauses": [], "gauge_step": 1.5}, TypeError),
            ({"num_vars": 3, "clauses": [], "gauge_step": True}, TypeError),
            ({"num_vars": 3, "clauses": [(1, 2, 3)]}, TypeError),
            ({"num_vars": 3, "clauses": [[1, 2, 3.0]]}, TypeError),
            ({"num_vars": 3, "clauses": [[1, 2, True]]}, TypeError),
        ]
        for kwargs, error in type_cases:
            with self.subTest(kwargs=kwargs):
                with self.assertRaises(error):
                    ConformalLagrangianSATSolver(**kwargs)

        value_cases = [
            {"num_vars": 0, "clauses": []},
            {"num_vars": -1, "clauses": []},
            {"num_vars": 3, "clauses": [], "max_flips": -1},
            {"num_vars": 3, "clauses": [], "gauge_step": 0},
            {"num_vars": 3, "clauses": [], "gauge_step": -1},
        ]
        for kwargs in value_cases:
            with self.subTest(kwargs=kwargs):
                with self.assertRaises(ValueError):
                    ConformalLagrangianSATSolver(**kwargs)


class TestIncrementalState(unittest.TestCase):
    def test_hypothetical_delta_matches_full_recomputation(self):
        rng = random.Random(71021)
        for case in range(100):
            n = rng.randint(3, 8)
            clauses = []
            for _ in range(rng.randint(1, 30)):
                variables = rng.sample(range(1, n + 1), 3)
                clauses.append(
                    [v if rng.getrandbits(1) else -v for v in variables]
                )

            solver = ConformalLagrangianSATSolver(n, clauses)
            assignment = [rng.randint(0, 1) for _ in range(n)]
            sat_count = [
                solver.clause_sat_count(i, assignment)
                for i in range(solver.m)
            ]
            lambdas = [rng.randint(1, 30) for _ in range(solver.m)]
            old_cost = explicit_weighted_cost(solver, assignment, lambdas)

            for v in range(n):
                before_assignment = assignment.copy()
                before_counts = sat_count.copy()
                before_lambdas = lambdas.copy()

                delta = solver.hypothetical_flip_delta(
                    v, assignment, sat_count, lambdas
                )
                flipped = assignment.copy()
                flipped[v] ^= 1
                expected_delta = (
                    explicit_weighted_cost(solver, flipped, lambdas) - old_cost
                )

                self.assertEqual(delta, expected_delta, (case, v))
                self.assertEqual(assignment, before_assignment)
                self.assertEqual(sat_count, before_counts)
                self.assertEqual(lambdas, before_lambdas)

    def test_apply_flip_matches_full_recomputation(self):
        rng = random.Random(8821)
        n = 12
        clauses = []
        for _ in range(60):
            variables = rng.sample(range(1, n + 1), 3)
            clauses.append(
                [v if rng.getrandbits(1) else -v for v in variables]
            )

        solver = ConformalLagrangianSATSolver(n, clauses)
        assignment = [rng.randint(0, 1) for _ in range(n)]
        sat_count, _, unsat, _ = solver.initialize_state(assignment)

        for _ in range(250):
            solver.apply_flip(
                rng.randrange(n), assignment, sat_count, unsat
            )
            expected_counts = [
                solver.clause_sat_count(i, assignment)
                for i in range(solver.m)
            ]
            expected_unsat = {
                i for i, count in enumerate(expected_counts) if count == 0
            }
            self.assertEqual(sat_count, expected_counts)
            self.assertEqual(unsat, expected_unsat)


class TestSolverBehavior(unittest.TestCase):
    def test_initial_all_zero_assignment_is_returned_when_valid(self):
        clauses = [[-1, 2, 3], [-1, -2, -3]]
        solver = ConformalLagrangianSATSolver(3, clauses)
        self.assertEqual(solver.solve(), [0, 0, 0])

    def test_equal_cost_tie_uses_lowest_variable_index(self):
        solver = ConformalLagrangianSATSolver(
            3, [[1, 2, 3]], max_flips=1
        )
        self.assertEqual(solver.solve(), [1, 0, 0])

    def test_base_formula(self):
        solver = ConformalLagrangianSATSolver(6, BASE_CLAUSES)
        solution = solver.solve()
        self.assertEqual(solution, [1, 0, 0, 0, 0, 0])
        self.assertTrue(solver.verify_solution(solution))

    def test_deterministic_across_runs(self):
        n, clauses, _ = generate_satisfiable_bench(20, 80, seed=2026)
        results = [
            ConformalLagrangianSATSolver(
                n, clauses, max_flips=10_000
            ).solve()
            for _ in range(5)
        ]
        self.assertTrue(all(result == results[0] for result in results))
        self.assertTrue(
            ConformalLagrangianSATSolver(n, clauses).verify_solution(
                results[0]
            )
        )

    def test_known_unsatisfiable_formula_returns_none_at_limit(self):
        # The eight sign patterns forbid all eight assignments of x1,x2,x3.
        clauses = [
            [signs[i] * (i + 1) for i in range(3)]
            for signs in itertools.product((-1, 1), repeat=3)
        ]
        solver = ConformalLagrangianSATSolver(
            3, clauses, max_flips=100
        )
        self.assertIsNone(solver.solve())

    def test_zero_flip_boundary(self):
        initially_valid = ConformalLagrangianSATSolver(
            3, [[-1, -2, -3]], max_flips=0
        )
        needs_flip = ConformalLagrangianSATSolver(
            3, [[1, 2, 3]], max_flips=0
        )
        self.assertEqual(initially_valid.solve(), [0, 0, 0])
        self.assertIsNone(needs_flip.solve())

    def test_empty_formula(self):
        solver = ConformalLagrangianSATSolver(4, [])
        self.assertEqual(solver.solve(), [0, 0, 0, 0])
        self.assertTrue(solver.verify_solution([0, 0, 0, 0]))

    def test_exhaustive_canonical_n3_formulas(self):
        # These 8 clauses each forbid one of the 8 assignments. Test all
        # 256 subsets. Only the complete set is UNSAT.
        canonical = [
            [signs[i] * (i + 1) for i in range(3)]
            for signs in itertools.product((-1, 1), repeat=3)
        ]
        for mask in range(256):
            clauses = [
                canonical[i] for i in range(8) if (mask >> i) & 1
            ]
            solver = ConformalLagrangianSATSolver(
                3, clauses, max_flips=500
            )
            result = solver.solve()
            if mask == 255:
                self.assertIsNone(result, mask)
            else:
                self.assertIsNotNone(result, mask)
                self.assertTrue(solver.verify_solution(result), mask)

    def test_random_small_formulas_against_brute_force(self):
        rng = random.Random(123456)
        for case in range(120):
            n = rng.randint(3, 6)
            clauses = []
            for _ in range(rng.randint(0, 24)):
                variables = rng.sample(range(1, n + 1), 3)
                clauses.append(
                    [v if rng.getrandbits(1) else -v for v in variables]
                )

            reference = brute_force_solution(n, clauses)
            solver = ConformalLagrangianSATSolver(
                n, clauses, max_flips=1_500
            )
            result = solver.solve()

            # Soundness is mandatory: every returned assignment must verify.
            if result is not None:
                self.assertTrue(solver.verify_solution(result), case)

            # On this exhaustive small corpus, compare success/None to the
            # complete brute-force oracle as a practical regression test.
            self.assertEqual(result is None, reference is None, case)


class TestBenchmarkGenerator(unittest.TestCase):
    def test_generator_validation(self):
        for n_vars in (2, 1, 0, -1):
            with self.subTest(n_vars=n_vars):
                with self.assertRaises(ValueError):
                    generate_satisfiable_bench(n_vars, 1)

        with self.assertRaises(TypeError):
            generate_satisfiable_bench(3.5, 1)
        with self.assertRaises(TypeError):
            generate_satisfiable_bench(3, 1.5)

        # bool is a subclass of int in Python, but the API must reject it.
        with self.assertRaises(TypeError):
            generate_satisfiable_bench(True, 1)
        with self.assertRaises(TypeError):
            generate_satisfiable_bench(False, 1)
        with self.assertRaises(TypeError):
            generate_satisfiable_bench(3, True)
        with self.assertRaises(TypeError):
            generate_satisfiable_bench(3, False)

        with self.assertRaises(ValueError):
            generate_satisfiable_bench(3, -1)

    def test_generator_does_not_modify_global_rng_state(self):
        random.seed(918273)
        state_before = random.getstate()
        generate_satisfiable_bench(10, 20, seed=55)
        state_after = random.getstate()
        self.assertEqual(state_after, state_before)

    def test_generator_is_reproducible_and_solution_is_planted(self):
        first = generate_satisfiable_bench(20, 80, seed=2026)
        second = generate_satisfiable_bench(20, 80, seed=2026)
        self.assertEqual(first, second)

        n, clauses, planted = first
        self.assertEqual(n, 20)
        self.assertEqual(len(clauses), 80)
        self.assertTrue(all(len(c) == 3 for c in clauses))
        self.assertTrue(
            all(len({abs(lit) for lit in c}) == 3 for c in clauses)
        )
        verifier = ConformalLagrangianSATSolver(n, clauses)
        self.assertTrue(verifier.verify_solution(planted))

    def test_requested_dense_benchmark_is_solved(self):
        n, clauses, _ = generate_satisfiable_bench(20, 80, seed=2026)
        solver = ConformalLagrangianSATSolver(
            n, clauses, max_flips=10_000, gauge_step=1
        )
        result = solver.solve()
        self.assertIsNotNone(result)
        self.assertTrue(solver.verify_solution(result))

    def test_multiple_positive_gauge_steps(self):
        n, clauses, _ = generate_satisfiable_bench(20, 85, seed=31415)
        for gauge_step in (1, 2, 7):
            with self.subTest(gauge_step=gauge_step):
                solver = ConformalLagrangianSATSolver(
                    n, clauses, max_flips=10_000, gauge_step=gauge_step
                )
                result = solver.solve()
                self.assertIsNotNone(result)
                self.assertTrue(solver.verify_solution(result))


if __name__ == "__main__":
    unittest.main(verbosity=2)
