import Mathlib.Data.Set.Insert
import Erdos107.ConvexAlternating
import Erdos107.Bridge
import Erdos107.OrderType

namespace ErdosSzekeres

/-- Inside-triangle predicate for an abstract order type. -/
def InsideTriangle {N : ℕ} (ot : OrderType N) (a b c p : Fin N) : Prop :=
  ot.σ a b p = ot.σ a b c ∧ ot.σ b c p = ot.σ a b c ∧ ot.σ c a p = ot.σ a b c

/-- For real points, convex-hull inclusion implies the inside-triangle predicate. -/
lemma insideTriangle_of_convexHull_triangle {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) {a b c d : Fin N}
    (habc : Distinct3 a b c) (habd : Distinct3 a b d)
    (hbcd : Distinct3 b c d) (hcad : Distinct3 c a d)
    (hd : p d ∈ convexHull ℝ ({p a, p b, p c} : Set Plane)) :
    InsideTriangle (orderTypeOfPoints p hp) a b c d := by
  classical
  have h1 : decide (det3 p a b d > 0) = decide (det3 p a b c > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := a) (b := b) (c := c) (d := d) habc habd hd
  have hset_bca : ({p b, p c, p a} : Set Plane) = ({p a, p b, p c} : Set Plane) := by
    ext x
    simp [Set.insert_comm, Set.pair_comm, or_left_comm, or_assoc, or_comm]
  have hd_bca : p d ∈ convexHull ℝ ({p b, p c, p a} : Set Plane) := by
    simpa [hset_bca] using hd
  have h2 : decide (det3 p b c d > 0) = decide (det3 p b c a > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := b) (b := c) (c := a) (d := d)
      (by
        rcases habc with ⟨hab, hac, hbc⟩
        exact ⟨hbc, by simpa [eq_comm] using hab, by simpa [eq_comm] using hac⟩)
      hbcd hd_bca
  have hset_cab : ({p c, p a, p b} : Set Plane) = ({p a, p b, p c} : Set Plane) := by
    ext x
    simp [Set.insert_comm, Set.pair_comm, or_left_comm, or_assoc, or_comm]
  have hd_cab : p d ∈ convexHull ℝ ({p c, p a, p b} : Set Plane) := by
    simpa [hset_cab] using hd
  have h3 : decide (det3 p c a d > 0) = decide (det3 p c a b > 0) :=
    det3_same_sign_of_convexHull_triangle (p := p) (hp := hp)
      (a := c) (b := a) (c := b) (d := d)
      (by
        rcases habc with ⟨hab, hac, hbc⟩
        exact ⟨by simpa [eq_comm] using hac, by simpa [eq_comm] using hbc, hab⟩)
      hcad hd_cab
  refine ⟨?_, ?_, ?_⟩
  · simpa [orderTypeOfPoints] using h1
  · -- align `b,c,a` with the `(a,b,c)` orientation
    have h2' : decide (det3 p b c a > 0) = decide (det3 p a b c > 0) := by
      simpa [det3_cycle (p := p) a b c]
    have h2'' : decide (det3 p b c d > 0) = decide (det3 p a b c > 0) := by
      simpa [h2'] using h2
    simpa [orderTypeOfPoints] using h2''
  · have h3' : decide (det3 p c a b > 0) = decide (det3 p a b c > 0) := by
      simpa [det3_cycle (p := p) c a b]
    have h3'' : decide (det3 p c a d > 0) = decide (det3 p a b c > 0) := by
      simpa [h3'] using h3
    simpa [orderTypeOfPoints] using h3''

/-- Index order agrees with increasing x-coordinate. -/
def XOrdered {N : ℕ} (p : Fin N → Plane) : Prop :=
  ∀ {i j : Fin N}, i < j → p i 0 < p j 0

/-- Signotope axioms (CNF form) for every increasing 4-tuple. -/
def SignotopeAxioms {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ a b c d : Fin N, a < b → b < c → c < d →
    ((ot.σ a b c = false) ∨ (ot.σ a b d = true) ∨ (ot.σ a c d = false) ∨ (ot.σ b c d = true)) ∧
    ((ot.σ a b c = true) ∨ (ot.σ a b d = false) ∨ (ot.σ a c d = true) ∨ (ot.σ b c d = false))


/-- Distinctness for an increasing 4-tuple. -/
lemma distinct4_of_lt {N : ℕ} {a b c d : Fin N} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    Distinct4 a b c d := by
  refine ⟨ne_of_lt hab, ?_, ?_, ne_of_lt hbc, ?_, ne_of_lt hcd⟩
  · exact ne_of_lt (lt_trans hab hbc)
  · exact ne_of_lt (lt_trans (lt_trans hab hbc) hcd)
  · exact ne_of_lt (lt_trans hbc hcd)

/-- Acyclicity implies the signotope axioms (for any order type). -/
lemma acyclic_imp_signotope {N : ℕ} (ot : OrderType N) (hacyc : OrderType.Acyclic ot) :
    SignotopeAxioms ot := by
  intro a b c d hab hbc hcd
  have hdist0 : Distinct4 a b c d := distinct4_of_lt hab hbc hcd
  rcases hdist0 with ⟨hab', hac', had', hbc', hbd', hcd'⟩
  have hdist' : Distinct4 a b d c := by
    exact ⟨hab', had', hac', hbd', hbc', by simpa [eq_comm] using hcd'⟩
  have hacyc1 :
      (ot.σ a b c = false) ∨ (ot.σ d b c = true) ∨ (ot.σ a d c = true) ∨ (ot.σ a b d = true) :=
    hacyc a b c d ⟨hab', hac', had', hbc', hbd', hcd'⟩
  have hacyc2 :
      (ot.σ a b d = false) ∨ (ot.σ c b d = true) ∨ (ot.σ a c d = true) ∨ (ot.σ a b c = true) :=
    hacyc a b d c hdist'
  -- rewrite pieces of hacyc1
  have hdbc : ot.σ d b c = ot.σ b c d := by
    have hdbc' : Distinct3 d b c := by
      exact ⟨by symm; exact hbd', by symm; exact hcd', hbc'⟩
    simpa using (ot.cycle (i := d) (j := b) (k := c) hdbc')
  have hadc : ot.σ a d c = ! ot.σ a c d := by
    have hadc' : Distinct3 a d c := by
      exact ⟨had', hac', by symm; exact hcd'⟩
    have h1 := ot.swap12 (i := a) (j := d) (k := c) hadc'
    have h2 : ot.σ d a c = ot.σ a c d := by
      have hdac : Distinct3 d a c := by
        exact ⟨by symm; exact had', by symm; exact hcd', hac'⟩
      simpa using (ot.cycle (i := d) (j := a) (k := c) hdac)
    simpa [h2] using h1
  have hcl1 :
      (ot.σ a b c = false) ∨
      (ot.σ a b d = true) ∨
      (ot.σ a c d = false) ∨
      (ot.σ b c d = true) := by
    -- reorder to match SignotopeAxioms clause
    -- hacyc1: ¬σ(abc) ∨ σ(dbc) ∨ σ(adc) ∨ σ(abd)
    -- after rewriting dbc/ad c
    -- we want: ¬σ(abc) ∨ σ(abd) ∨ ¬σ(acd) ∨ σ(bcd)
    have h1' :
        (ot.σ a b c = false) ∨
        (ot.σ b c d = true) ∨
        (ot.σ a c d = false) ∨
        (ot.σ a b d = true) := by
      simpa [hdbc, hadc] using hacyc1
    -- reorder disjunctions
    simpa [or_left_comm, or_comm, or_assoc] using h1'
  -- rewrite pieces of hacyc2
  have hcbd : ot.σ c b d = ! ot.σ b c d := by
    have hcbd' : Distinct3 c b d := by
      exact ⟨by symm; exact hbc', hcd', hbd'⟩
    simpa using (ot.swap12 (i := c) (j := b) (k := d) hcbd')
  have hcl2 :
      (ot.σ a b c = true) ∨
      (ot.σ a b d = false) ∨
      (ot.σ a c d = true) ∨
      (ot.σ b c d = false) := by
    have h2' :
        (ot.σ a b d = false) ∨
        (ot.σ b c d = false) ∨
        (ot.σ a c d = true) ∨
        (ot.σ a b c = true) := by
      simpa [hcbd] using hacyc2
    simpa [or_left_comm, or_comm, or_assoc] using h2'
  exact ⟨hcl1, hcl2⟩

/-- For real points in general position, the induced order type is a signotope. -/
lemma orderTypeOfPoints_signotope {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) :
    SignotopeAxioms (orderTypeOfPoints p hp) := by
  exact acyclic_imp_signotope (ot := orderTypeOfPoints p hp) (orderTypeOfPoints_acyclic p hp)

def CCInteriority {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ p q r t : Fin N, Distinct4 p q r t →
    ot.σ t q r = true → ot.σ p t r = true → ot.σ p q t = true → ot.σ p q r = true

/-- Pairwise distinctness for a 5-tuple. -/
def Distinct5 {N : ℕ} (a b c d e : Fin N) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
  b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
  c ≠ d ∧ c ≠ e ∧ d ≠ e

/-- CC-system transitivity axiom. -/
def CCTransitivity {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ t s p q r : Fin N, Distinct5 t s p q r →
    ot.σ t s p = true → ot.σ t s q = true → ot.σ t s r = true →
    ot.σ t p q = true → ot.σ t q r = true → ot.σ t p r = true

/-- Full CC-system: interiority + transitivity. -/
def CCSystem {N : ℕ} (ot : OrderType N) : Prop :=
  CCInteriority ot ∧ CCTransitivity ot

/-- CC-interiority for real points in general position. -/
theorem orderTypeOfPoints_ccInteriority {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) : CCInteriority (orderTypeOfPoints p hp) := by
  classical
  intro i j k t hdist htjk hitk hijk
  have htjk' : det3 p t j k > 0 := by
    simpa [orderTypeOfPoints] using htjk
  have hitk' : det3 p i t k > 0 := by
    simpa [orderTypeOfPoints] using hitk
  have hijk' : det3 p i j t > 0 := by
    simpa [orderTypeOfPoints] using hijk
  have h1 : det3 p j k t > 0 := by
    simpa [det3_cycle (p := p) t j k] using htjk'
  have h2a : det3 p t k i > 0 := by
    simpa [det3_cycle (p := p) i t k] using hitk'
  have h2 : det3 p k i t > 0 := by
    simpa [det3_cycle (p := p) t k i] using h2a
  have hsum : det3 p i j t + det3 p j k t + det3 p k i t = det3 p i j k :=
    det3_sum (p := p) i j k t
  have hpos : det3 p i j k > 0 := by
    linarith [hsum, hijk', h1, h2]
  simpa [orderTypeOfPoints] using hpos

/-- Geometric transitivity for oriented areas in the plane. -/
theorem det3_transitivity {N : ℕ} (p : Fin N → Plane)
    {t s a b c : Fin N} :
    det3 p t s a > 0 → det3 p t s b > 0 → det3 p t s c > 0 →
    det3 p t a b > 0 → det3 p t b c > 0 → det3 p t a c > 0 := by
  classical
  intro htsa htsb htsc htab htbc
  set u : Plane := p s - p t
  set v : Plane := p a - p t
  set w : Plane := p b - p t
  set z : Plane := p c - p t
  have huv : det2 u v > 0 := by simpa [det3, u, v] using htsa
  have huw : det2 u w > 0 := by simpa [det3, u, w] using htsb
  have huz : det2 u z > 0 := by simpa [det3, u, z] using htsc
  have hvw : det2 v w > 0 := by simpa [det3, v, w] using htab
  have hwz : det2 w z > 0 := by simpa [det3, w, z] using htbc
  set D : ℝ := u 0 * u 0 + u 1 * u 1
  have hDne : D ≠ 0 := by
    intro hD0
    have h0 : u 0 = 0 ∧ u 1 = 0 := by
      have : u 0 * u 0 + u 1 * u 1 = 0 := by simpa [D] using hD0
      exact (mul_self_add_mul_self_eq_zero.mp this)
    have hu : u = 0 := by
      ext i; fin_cases i <;> simp [h0.1, h0.2]
    have : det2 u v = 0 := by simp [hu, det2]
    exact (ne_of_gt huv) this
  have hDpos : 0 < D := by
    have hDnonneg : 0 ≤ D := by
      have h0 : 0 ≤ u 0 * u 0 := by nlinarith
      have h1 : 0 ≤ u 1 * u 1 := by nlinarith
      nlinarith [h0, h1]
    exact lt_of_le_of_ne hDnonneg (Ne.symm hDne)
  let acoef (x : Plane) : ℝ := (u 0 * x 0 + u 1 * x 1) / D
  let bcoef (x : Plane) : ℝ := det2 u x / D
  have hdet2_uv : det2 u v = D * bcoef v := by
    dsimp [bcoef]
    calc
      det2 u v = (D * det2 u v) / D := by
        symm; exact (mul_div_cancel_left₀ (det2 u v) hDne)
      _ = D * (det2 u v / D) := by
        simpa using (mul_div_assoc D (det2 u v) D)
  have hdet2_uw : det2 u w = D * bcoef w := by
    dsimp [bcoef]
    calc
      det2 u w = (D * det2 u w) / D := by
        symm; exact (mul_div_cancel_left₀ (det2 u w) hDne)
      _ = D * (det2 u w / D) := by
        simpa using (mul_div_assoc D (det2 u w) D)
  have hdet2_uz : det2 u z = D * bcoef z := by
    dsimp [bcoef]
    calc
      det2 u z = (D * det2 u z) / D := by
        symm; exact (mul_div_cancel_left₀ (det2 u z) hDne)
      _ = D * (det2 u z / D) := by
        simpa using (mul_div_assoc D (det2 u z) D)
  have hdet2_vw : det2 v w = D * acoef v * bcoef w - D * acoef w * bcoef v := by
    dsimp [acoef, bcoef, det2]
    field_simp [hDne]
    simp [D]
    ring_nf
  have hdet2_wz : det2 w z = D * acoef w * bcoef z - D * acoef z * bcoef w := by
    dsimp [acoef, bcoef, det2]
    field_simp [hDne]
    simp [D]
    ring_nf
  have hbv : 0 < bcoef v := by
    have : 0 < D * bcoef v := by simpa [hdet2_uv] using huv
    exact (mul_pos_iff_of_pos_left hDpos).1 this
  have hbw : 0 < bcoef w := by
    have : 0 < D * bcoef w := by simpa [hdet2_uw] using huw
    exact (mul_pos_iff_of_pos_left hDpos).1 this
  have hbz : 0 < bcoef z := by
    have : 0 < D * bcoef z := by simpa [hdet2_uz] using huz
    exact (mul_pos_iff_of_pos_left hDpos).1 this
  have hvw' : 0 < acoef v * bcoef w - acoef w * bcoef v := by
    have htmp : 0 < D * acoef v * bcoef w - D * acoef w * bcoef v :=
      by simpa [hdet2_vw] using hvw
    have htmp' : 0 < D * (acoef v * bcoef w - acoef w * bcoef v) := by
      -- factor out D
      have : D * acoef v * bcoef w - D * acoef w * bcoef v =
          D * (acoef v * bcoef w - acoef w * bcoef v) := by ring_nf
      simpa [this] using htmp
    exact (mul_pos_iff_of_pos_left hDpos).1 htmp'
  have hwz' : 0 < acoef w * bcoef z - acoef z * bcoef w := by
    have htmp : 0 < D * acoef w * bcoef z - D * acoef z * bcoef w :=
      by simpa [hdet2_wz] using hwz
    have htmp' : 0 < D * (acoef w * bcoef z - acoef z * bcoef w) := by
      have : D * acoef w * bcoef z - D * acoef z * bcoef w =
          D * (acoef w * bcoef z - acoef z * bcoef w) := by ring_nf
      simpa [this] using htmp
    exact (mul_pos_iff_of_pos_left hDpos).1 htmp'
  have hvw_lt : acoef w * bcoef v < acoef v * bcoef w := by linarith [hvw']
  have hwz_lt : acoef z * bcoef w < acoef w * bcoef z := by linarith [hwz']
  have hvw_mul : acoef w * bcoef v * bcoef z < acoef v * bcoef w * bcoef z := by
    have h := mul_lt_mul_of_pos_right hvw_lt hbz
    simpa [mul_assoc] using h
  have hwz_mul : acoef z * bcoef w * bcoef v < acoef w * bcoef v * bcoef z := by
    have h := mul_lt_mul_of_pos_right hwz_lt hbv
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hchain : acoef z * bcoef w * bcoef v < acoef v * bcoef w * bcoef z :=
    lt_trans hwz_mul hvw_mul
  have hfinal : acoef z * bcoef v < acoef v * bcoef z := by
    have hchain' : bcoef w * (acoef z * bcoef v) < bcoef w * (acoef v * bcoef z) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
    exact (lt_of_mul_lt_mul_left hchain' (show 0 ≤ bcoef w from le_of_lt hbw))
  have htac' : 0 < acoef v * bcoef z - acoef z * bcoef v := by
    linarith [hfinal]
  have hdet2_vz : det2 v z = D * acoef v * bcoef z - D * acoef z * bcoef v := by
    dsimp [acoef, bcoef, det2]
    field_simp [hDne]
    simp [D]
    ring_nf
  have : det2 v z > 0 := by
    have : 0 < D * acoef v * bcoef z - D * acoef z * bcoef v := by
      have : 0 < D * (acoef v * bcoef z - acoef z * bcoef v) :=
        (mul_pos_iff_of_pos_left hDpos).2 htac'
      simpa [mul_sub, mul_left_comm, mul_assoc, mul_comm] using this
    simpa [hdet2_vz] using this
  simpa [det3, v, z] using this

/-- CC-transitivity for real points in general position. -/
theorem orderTypeOfPoints_ccTransitivity {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) : CCTransitivity (orderTypeOfPoints p hp) := by
  classical
  intro t s a b c hdist hts_a hts_b hts_c htab htbc
  have hts_a' : det3 p t s a > 0 := by simpa [orderTypeOfPoints] using hts_a
  have hts_b' : det3 p t s b > 0 := by simpa [orderTypeOfPoints] using hts_b
  have hts_c' : det3 p t s c > 0 := by simpa [orderTypeOfPoints] using hts_c
  have htab' : det3 p t a b > 0 := by simpa [orderTypeOfPoints] using htab
  have htbc' : det3 p t b c > 0 := by simpa [orderTypeOfPoints] using htbc
  have htac' : det3 p t a c > 0 :=
    det3_transitivity (p := p) (t := t) (s := s) (a := a) (b := b) (c := c)
      hts_a' hts_b' hts_c' htab' htbc'
  simpa [orderTypeOfPoints] using htac'

/-- For real points in general position, the induced order type satisfies CC-system axioms. -/
theorem orderTypeOfPoints_ccSystem {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) : CCSystem (orderTypeOfPoints p hp) := by
  refine ⟨orderTypeOfPoints_ccInteriority (p := p) (hp := hp), ?_⟩
  exact orderTypeOfPoints_ccTransitivity (p := p) (hp := hp)

/-- No-convex-6-gon condition in inside-triangle form (for a fixed order type). -/
def No6GonClause {N : ℕ} (ot : OrderType N) : Prop :=
  ∀ f : Fin 6 ↪ Fin N,
    ∃ i a b c : Fin 6, Distinct4 i a b c ∧
      InsideTriangle ot (f a) (f b) (f c) (f i)

/-- Distinctness is preserved by embeddings. -/
lemma Distinct4.map {N M : ℕ} (f : Fin N ↪ Fin M) {a b c d : Fin N} :
    Distinct4 a b c d → Distinct4 (f a) (f b) (f c) (f d) := by
  intro h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h'; exact h.1 (f.injective h')
  · intro h'; exact h.2.1 (f.injective h')
  · intro h'; exact h.2.2.1 (f.injective h')
  · intro h'; exact h.2.2.2.1 (f.injective h')
  · intro h'; exact h.2.2.2.2.1 (f.injective h')
  · intro h'; exact h.2.2.2.2.2 (f.injective h')

/-- If a 6-point configuration is not convex independent, one point is in the convex hull
    of the other five. -/
lemma not_convexIndependent_imp_mem_convexHull_univ {q : Fin 6 → Plane} :
    ¬ ConvexIndependent ℝ q →
      ∃ i : Fin 6, q i ∈ convexHull ℝ (q '' (Set.univ \ {i})) := by
  classical
  intro hnot
  have h :=
    (convexIndependent_iff_notMem_convexHull_diff (p := q) (𝕜 := ℝ)).not.mp hnot
  push_neg at h
  rcases h with ⟨i, s, hi⟩
  have hsubset : s \ {i} ⊆ (Set.univ \ {i}) := by
    intro x hx
    exact ⟨by trivial, hx.2⟩
  have himage : q '' (s \ {i}) ⊆ q '' (Set.univ \ {i}) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, hsubset hy, rfl⟩
  have hmono : convexHull ℝ (q '' (s \ {i})) ⊆ convexHull ℝ (q '' (Set.univ \ {i})) :=
    convexHull_mono himage
  exact ⟨i, hmono hi⟩

/-- Carathéodory (triangle form) for points in the plane. -/
theorem mem_convexHull_triangle_of_mem_convexHull {N : ℕ} {p : Fin N → Plane} {i : Fin N}
    (hN : 4 ≤ N) :
    p i ∈ convexHull ℝ (p '' (Set.univ \ {i})) →
      ∃ a b c : Fin N, Distinct4 i a b c ∧
        p i ∈ convexHull ℝ ({p a, p b, p c} : Set Plane) := by
  classical
  intro hi
  obtain ⟨u, hu_sub, hu_card, hi_u⟩ :=
    mem_convexHull_image_finset_card_le_three (p := p)
      (s := (Set.univ \ {i})) (i := i) hi
  have hu_sub' : u ⊆ Finset.univ.erase i := by
    intro x hx
    have hx' : x ∈ (Set.univ \ {i}) := hu_sub (by simpa using hx)
    have hxne : x ≠ i := hx'.2
    simp [Finset.mem_erase, hxne]
  have hcard_t : 3 ≤ (Finset.univ.erase i).card := by
    have hcard : (Finset.univ.erase i).card = N - 1 := by
      simpa using (Finset.card_erase (s := Finset.univ) (a := i))
    have h' : 3 ≤ N - 1 := by
      have h'' : 4 - 1 ≤ N - 1 := Nat.sub_le_sub_right hN 1
      simpa using h''
    simpa [hcard] using h'
  obtain ⟨v, huv, hvu, hvcard⟩ :=
    Finset.exists_subsuperset_card_eq (s := u) (t := Finset.univ.erase i) (n := 3)
      hu_sub' (by simpa using hu_card) (by simpa using hcard_t)
  obtain ⟨a, b, c, hab, hac, hbc, hv_eq⟩ := (Finset.card_eq_three).1 (by simpa using hvcard)
  have ha_mem : a ∈ Finset.univ.erase i := hvu (by simp [hv_eq])
  have hb_mem : b ∈ Finset.univ.erase i := hvu (by simp [hv_eq])
  have hc_mem : c ∈ Finset.univ.erase i := hvu (by simp [hv_eq])
  have hai' : a ≠ i := by simpa using ha_mem
  have hbi' : b ≠ i := by simpa using hb_mem
  have hci' : c ≠ i := by simpa using hc_mem
  have hsubset : p '' (↑u : Set (Fin N)) ⊆ p '' (↑v : Set (Fin N)) := by
    intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    have hj' : j ∈ v := huv (by simpa using hj)
    exact ⟨j, by simpa using hj', rfl⟩
  have hi_v : p i ∈ convexHull ℝ (p '' (↑v : Set (Fin N))) :=
    convexHull_mono hsubset hi_u
  have hset : p '' ({a, b, c} : Set (Fin N)) = ({p a, p b, p c} : Set Plane) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y = a ∨ y = b ∨ y = c := by
        simpa using hy
      rcases hy' with rfl | rfl | rfl <;> simp
    · intro hx
      have hx' : x = p a ∨ x = p b ∨ x = p c := by
        simpa using hx
      rcases hx' with hx' | hx' | hx'
      · refine ⟨a, ?_, ?_⟩
        · simp
        · simpa [hx']
      · refine ⟨b, ?_, ?_⟩
        · simp
        · simpa [hx']
      · refine ⟨c, ?_, ?_⟩
        · simp
        · simpa [hx']
  have htri : p i ∈ convexHull ℝ ({p a, p b, p c} : Set Plane) := by
    have hi_v' : p i ∈ convexHull ℝ (p '' ({a, b, c} : Set (Fin N))) := by
      simpa [hv_eq] using hi_v
    simpa [hset] using hi_v'
  refine ⟨a, b, c, ?_, htri⟩
  refine ⟨?_, ?_, ?_, hab, hac, hbc⟩
  · simpa [eq_comm] using hai'
  · simpa [eq_comm] using hbi'
  · simpa [eq_comm] using hci'

/-- Soundness bridge (geometric): no convex 6-gon implies inside-triangle clauses. -/
theorem noConvex6_imp_No6GonClause {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) :
    (¬ HasConvexSubset (n := 6) p) → No6GonClause (orderTypeOfPoints p hp) := by
  classical
  intro hno f
  have hnot : ¬ ConvexIndependent ℝ (p ∘ f) := by
    intro hci
    exact hno ⟨f, hci⟩
  rcases not_convexIndependent_imp_mem_convexHull_univ (q := p ∘ f) hnot with ⟨i, hi⟩
  rcases mem_convexHull_triangle_of_mem_convexHull (p := p ∘ f) (i := i) (hN := by decide) hi with
    ⟨a, b, c, hdist, htri⟩
  have hdist_f : Distinct4 (f i) (f a) (f b) (f c) := Distinct4.map f hdist
  have habc : Distinct3 (f a) (f b) (f c) := by
    refine ⟨hdist_f.2.2.2.1, hdist_f.2.2.2.2.1, hdist_f.2.2.2.2.2⟩
  have habi : Distinct3 (f a) (f b) (f i) := by
    refine ⟨hdist_f.2.2.2.1, ?_, ?_⟩
    · simpa using hdist_f.1.symm
    · simpa using hdist_f.2.1.symm
  have hbci : Distinct3 (f b) (f c) (f i) := by
    refine ⟨hdist_f.2.2.2.2.2, ?_, ?_⟩
    · simpa using hdist_f.2.1.symm
    · simpa using hdist_f.2.2.1.symm
  have hcai : Distinct3 (f c) (f a) (f i) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa using hdist_f.2.2.2.2.1.symm
    · simpa using hdist_f.2.2.1.symm
    · simpa using hdist_f.1.symm
  have htri' :
      p (f i) ∈ convexHull ℝ ({p (f a), p (f b), p (f c)} : Set Plane) := by
    simpa [Function.comp] using htri
  have hinside :
      InsideTriangle (orderTypeOfPoints p hp) (f a) (f b) (f c) (f i) :=
    insideTriangle_of_convexHull_triangle (p := p) (hp := hp)
      (a := f a) (b := f b) (c := f c) (d := f i) habc habi hbci hcai htri'
  exact ⟨i, a, b, c, hdist, hinside⟩


end ErdosSzekeres
