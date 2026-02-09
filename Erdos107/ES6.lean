import Erdos107.ErdosSzekeres
import Erdos107.Bridge
import Erdos107.Certificates

namespace ErdosSzekeres

/-- Upper bound from the UNSAT certificate. -/
theorem ES_upper_bound_6 : ES 6 ≤ 17 := by
  classical
  have hwFn : ESWitnessFn 6 17 :=
    signotope_unsat_imp_ESWitnessFn_6_17 signotope_unsat_6_17
  have hw : ESWitness 6 17 := ESWitness_of_ESWitnessFn hwFn
  exact Nat.find_min' (exists_ES_witness 6) hw

/-- Lower bound from the 16-point witness. -/
theorem ES_lower_bound_6 : 17 ≤ ES 6 := by
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

/-- The ES(6) = 17 theorem (Szekeres & Peters, 2006). -/
theorem ES_six : ES 6 = 17 := by
  exact le_antisymm ES_upper_bound_6 ES_lower_bound_6

end ErdosSzekeres
