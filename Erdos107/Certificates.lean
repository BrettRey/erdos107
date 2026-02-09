import Erdos107.ErdosSzekeres
import Erdos107.SATCNF

namespace ErdosSzekeres

/-- Placeholder variable type for the signotope CNF instance. -/
axiom SignotopeVar : Type

/-- Signotope CNF instance for `N = 17` (GP3 + CC + full triangles). -/
axiom signotope_cnf_6_17 : CNF SignotopeVar

/-- SHA256 of the archived CNF instance. -/
def signotope_cnf_6_17_sha256 : String :=
  "ae73dd7d55a7646f8db847c4cea40a369a515415e7d362dfc4cf6301cdd41d75"

/-- SHA256 of the archived LRAT proof. -/
def signotope_lrat_6_17_sha256 : String :=
  "bccd829b3983efbb6d53a611da781fb42b8e44de096e7401b87f00ff98e96523"

/-- External UNSAT certificate for the signotope CNF instance. -/
axiom signotope_unsat_6_17 : ¬ Satisfiable signotope_cnf_6_17

/-- Soundness axiom: a geometric counterexample induces a satisfying assignment. -/
axiom signotope_geom_sound_6_17 :
  (∃ p : Fin 17 → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := 6) p) →
    Satisfiable signotope_cnf_6_17

/-- UNSAT of the signotope CNF implies the ES witness predicate. -/
theorem signotope_unsat_imp_ESWitnessFn_6_17 :
  ¬ Satisfiable signotope_cnf_6_17 → ESWitnessFn 6 17 := by
  intro hunsat p hp
  by_contra hconv
  have hgeom : ∃ p : Fin 17 → Plane, GeneralPositionFn p ∧ ¬ HasConvexSubset (n := 6) p :=
    ⟨p, hp, hconv⟩
  have hsat : Satisfiable signotope_cnf_6_17 := signotope_geom_sound_6_17 hgeom
  exact hunsat hsat

/-- Lower-bound witness: a 16-point set in general position with no convex 6-gon. -/
axiom lower_bound_witness_6_16 :
  ∃ s : Finset Plane, s.card = 16 ∧ Finset.GeneralPosition s ∧
    ¬ ∃ t : Finset Plane, t ⊆ s ∧ t.card = 6 ∧ Finset.ConvexPosition t

end ErdosSzekeres
