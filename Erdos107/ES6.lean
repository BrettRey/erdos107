import Erdos107.ErdosSzekeres
import Erdos107.Bridge
import Erdos107.Certificates

namespace ErdosSzekeres

/-- Upper bound from the UNSAT certificate. -/
theorem ES_upper_bound_6 : ES 6 ≤ 17 := by
  exact ES_upper_bound_6_from_certificate

/-- Lower bound from the 16-point witness. -/
theorem ES_lower_bound_6 : 17 ≤ ES 6 := by
  exact ES_lower_bound_6_from_witness

/-- The ES(6) = 17 theorem (Szekeres & Peters, 2006). -/
theorem ES_six : ES 6 = 17 := by
  exact le_antisymm ES_upper_bound_6 ES_lower_bound_6

end ErdosSzekeres
