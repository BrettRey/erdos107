import Erdos107.ErdosSzekeres
import Erdos107.SATCNF

namespace ErdosSzekeres

/-- Placeholder variable type for the signotope CNF instance. -/
axiom SignotopeVar : Type

/-- Signotope CNF instance for `N = 17` (GP3 + CC + full triangles). -/
axiom signotope_cnf_6_17 : CNF SignotopeVar

/-- Archive path for the CNF instance. -/
def signotope_cnf_6_17_path : String :=
  "artifacts/signotope-6-17/sig_6_17_gp3_cc_full.cnf"

/-- SHA256 of the archived CNF instance. -/
def signotope_cnf_6_17_sha256 : String :=
  "ae73dd7d55a7646f8db847c4cea40a369a515415e7d362dfc4cf6301cdd41d75"

/-- Archive path for the LRAT proof. -/
def signotope_lrat_6_17_path : String :=
  "artifacts/signotope-6-17/sig_6_17_gp3_cc_full.lrat"

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

/-- Upper bound ES(6) ≤ 17 from the UNSAT certificate. -/
theorem ES_upper_bound_6_from_certificate : ES 6 ≤ 17 := by
  classical
  have hwFn : ESWitnessFn 6 17 :=
    signotope_unsat_imp_ESWitnessFn_6_17 signotope_unsat_6_17
  have hw : ESWitness 6 17 := ESWitness_of_ESWitnessFn hwFn
  exact Nat.find_min' (exists_ES_witness 6) hw

/-- Lower-bound witness: a 16-point set in general position with no convex 6-gon. -/
axiom lower_bound_witness_6_16 :
  ∃ s : Finset Plane, s.card = 16 ∧ Finset.GeneralPosition s ∧
    ¬ ∃ t : Finset Plane, t ⊆ s ∧ t.card = 6 ∧ Finset.ConvexPosition t

/-- Archive path for the 16-point witness data. -/
def lower_bound_witness_6_16_path : String :=
  "artifacts/sig_witness_6_16.json"

/-- Lower bound ES(6) ≥ 17 from the 16-point witness. -/
theorem ES_lower_bound_6_from_witness : 17 ≤ ES 6 := by
  have hnot : ¬ ESWitness 6 16 := by
    intro hES
    rcases lower_bound_witness_6_16 with ⟨s, hs_card, hs_gp, hs_no⟩
    have h := hES s hs_card hs_gp
    rcases h with ⟨t, ht, ht_card, ht_conv⟩
    exact hs_no ⟨t, ht, ht_card, ht_conv⟩
  have hspec : ESWitness 6 (ES 6) := ES_spec 6
  have hgt : 16 < ES 6 := by
    by_contra hle
    have hle' : ES 6 ≤ 16 := le_of_not_gt hle
    have hES16 : ESWitness 6 16 := ESWitness.mono hle' hspec
    exact hnot hES16
  exact Nat.succ_le_of_lt hgt

end ErdosSzekeres
