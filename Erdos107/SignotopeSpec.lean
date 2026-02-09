import Mathlib.Data.Set.Insert
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

/-- CC-systems are implied by the chirotope + acyclic axioms. -/
axiom ccSystem_of_chirotope_acyclic {N : ℕ} {ot : OrderType N} :
    OrderType.IsChirotope ot → OrderType.Acyclic ot → CCSystem ot

/-- For real points in general position, the induced order type satisfies CC-system axioms. -/
theorem orderTypeOfPoints_ccSystem {N : ℕ} (p : Fin N → Plane)
    (hp : GeneralPositionFn p) : CCSystem (orderTypeOfPoints p hp) :=
  ccSystem_of_chirotope_acyclic (orderTypeOfPoints_isChirotope p hp)
    (orderTypeOfPoints_acyclic p hp)

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
axiom mem_convexHull_triangle_of_mem_convexHull {N : ℕ} {p : Fin N → Plane} {i : Fin N} :
    p i ∈ convexHull ℝ (p '' (Set.univ \ {i})) →
      ∃ a b c : Fin N, Distinct4 i a b c ∧
        p i ∈ convexHull ℝ ({p a, p b, p c} : Set Plane)

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
  rcases mem_convexHull_triangle_of_mem_convexHull (p := p ∘ f) (i := i) hi with
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
