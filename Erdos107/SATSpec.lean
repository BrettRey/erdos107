import Erdos107.OrderType

namespace ErdosSzekeres

/-- SAT-spec predicate: order-type axioms + acyclicity + avoidance of alternating n-subsets. -/
def SATSpec (n N : ℕ) (ot : OrderType N) : Prop :=
  OrderType.IsChirotope ot ∧ OrderType.Acyclic ot ∧ OrderType.AvoidsAlternating ot n

/-- A SAT-level counterexample: an order type satisfying the SAT spec. -/
def SATCounterexample (n N : ℕ) : Prop :=
  ∃ ot : OrderType N, SATSpec n N ot

end ErdosSzekeres
