import Erdos107.ErdosSzekeres
import Erdos107.SATCNF
import Erdos107.Blocked_6_17

namespace ErdosSzekeres

/-- UNSAT certificate: the SAT CNF for `N = 17` is unsatisfiable. -/
axiom unsat_6_17 : ¬ Satisfiable (SATCNF.satSpecCNF 6 17 blocked_6_17)

/-- Lower-bound witness: a 16-point set in general position with no convex 6-gon. -/
axiom lower_bound_witness_6_16 :
  ∃ s : Finset Plane, s.card = 16 ∧ Finset.GeneralPosition s ∧
    ¬ ∃ t : Finset Plane, t ⊆ s ∧ t.card = 6 ∧ Finset.ConvexPosition t

end ErdosSzekeres
