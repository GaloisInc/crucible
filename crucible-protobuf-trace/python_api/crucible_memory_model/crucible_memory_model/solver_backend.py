from typing_extensions import Self
import z3

class SolverBackend:
    def __init__(self,
                 solver: z3.Solver,
                 parent: Self = None,
                 proof_goals=None
                 ) -> Self:

        self.parent = parent

        self.solver = solver
        self.proof_goals = proof_goals or []
        self.assumptions = []

    def push(self):
        self.solver.push()

        # proof goals are shared and persisted, assumptions are not
        return SolverBackend(self.solver, parent=self, proof_goals=self.proof_goals)

    def pop(self):
        self.solver.pop()
        tail = self.parent
        self.parent = None
        return self, tail

    def add_assumption(self, assumption):
        self.assumptions.append(assumption)
        self.solver.add(assumption)

    def add_proof_goal(self, goal):
        self.proof_goals.append(goal)

    def satisfiable(self, *extra_assumptions):
        return self.solver.check(self.assumptions, *extra_assumptions) == z3.sat

