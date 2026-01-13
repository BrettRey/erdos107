import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Embedding.Basic

namespace ErdosSzekeres

/-- Pairwise distinctness for an ordered triple of indices. -/
def Distinct3 {N : ℕ} (i j k : Fin N) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

/-- Pairwise distinctness for an ordered quadruple of indices. -/
def Distinct4 {N : ℕ} (a b c d : Fin N) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- An order type (uniform rank-3 chirotope): assigns an orientation sign to each ordered triple
    of distinct indices. Here we represent the sign as `Bool` (two-valued, since we are in general
    position and never need the collinear/zero case). -/
structure OrderType (N : ℕ) where
  σ : Fin N → Fin N → Fin N → Bool
  swap12 : ∀ {i j k}, Distinct3 i j k → σ i j k = ! σ j i k
  cycle  : ∀ {i j k}, Distinct3 i j k → σ i j k = σ j k i

namespace OrderType

/-- Restrict/reindex an order type along an embedding of indices. -/
def reindex {N M : ℕ} (ot : OrderType M) (f : Fin N ↪ Fin M) : OrderType N :=
{ σ := fun i j k => ot.σ (f i) (f j) (f k)
, swap12 := by
    intro i j k h
    have h' : Distinct3 (f i) (f j) (f k) := by
      refine ⟨?_, ?_, ?_⟩
      · intro hij; exact h.1   (f.injective hij)
      · intro hik; exact h.2.1 (f.injective hik)
      · intro hjk; exact h.2.2 (f.injective hjk)
    simpa using ot.swap12 h'
, cycle := by
    intro i j k h
    have h' : Distinct3 (f i) (f j) (f k) := by
      refine ⟨?_, ?_, ?_⟩
      · intro hij; exact h.1   (f.injective hij)
      · intro hik; exact h.2.1 (f.injective hik)
      · intro hjk; exact h.2.2 (f.injective hjk)
    simpa using ot.cycle h'
}

end OrderType

namespace OrderType

/-- A cyclic order predicate on triples of indices (wrap-around allowed). -/
def CyclicTriple {n : ℕ} (i j k : Fin n) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

/-- The “alternating” (convex n-gon) sign pattern on triples of indices, as a Bool. -/
noncomputable def altσ {n : ℕ} (i j k : Fin n) : Bool :=
  by
    classical
    exact decide (CyclicTriple i j k)

/-- A labelled order type is alternating if its triple-sign function matches `altσ`
    on all distinct triples. -/
def IsAlternating {n : ℕ} (ot : ErdosSzekeres.OrderType n) : Prop :=
  ∀ i j k : Fin n, Distinct3 i j k → ot.σ i j k = altσ i j k

/-- An order type on `N` points *contains* an alternating `n`-subset if some embedding
    reindexes it to an alternating order type. -/
def ContainsAlternating {N : ℕ} (ot : ErdosSzekeres.OrderType N) (n : ℕ) : Prop :=
  ∃ f : Fin n ↪ Fin N, IsAlternating (ErdosSzekeres.OrderType.reindex ot f)

/-- An order type avoids an alternating `n`-subset if every embedding fails to be alternating. -/
def AvoidsAlternating {N : ℕ} (ot : ErdosSzekeres.OrderType N) (n : ℕ) : Prop :=
  ∀ f : Fin n ↪ Fin N, ¬ IsAlternating (ErdosSzekeres.OrderType.reindex ot f)

/-- Avoiding alternating subsets is just the negation of containing one. -/
lemma AvoidsAlternating_iff_not_contains {N : ℕ} (ot : ErdosSzekeres.OrderType N) (n : ℕ) :
    AvoidsAlternating ot n ↔ ¬ ContainsAlternating ot n := by
  constructor
  · intro h hn
    rcases hn with ⟨f, hf⟩
    exact (h f) hf
  · intro h f hf
    exact h ⟨f, hf⟩

/-- Lift an alternating subset from a reindexed order type back to the original one. -/
lemma ContainsAlternating.of_reindex {n N M : ℕ} {ot : ErdosSzekeres.OrderType M}
    (f : Fin N ↪ Fin M) :
    ContainsAlternating (ot := ErdosSzekeres.OrderType.reindex ot f) n →
      ContainsAlternating ot n := by
  rintro ⟨g, hg⟩
  let fg : Fin n ↪ Fin M :=
    ⟨fun i => f (g i), by
      intro i j h
      exact g.injective (f.injective h)⟩
  refine ⟨fg, ?_⟩
  intro i j k hijk
  -- `hg` is alternatingness of `reindex (reindex ot f) g`; unfold to get
  -- alternatingness of `reindex ot fg`.
  simpa [IsAlternating, ErdosSzekeres.OrderType.reindex, fg] using (hg i j k hijk)

end OrderType

namespace OrderType

/-- “Sign multiplication” for Bool-coded signs: True = `+`, False = `-`.
    The product is `+` iff the signs are equal. -/
def signMul (x y : Bool) : Bool :=
  decide (x = y)

/-- Rank-3 Grassmann–Plücker relation in Bool form for five indices.
    (This statement only makes sense when all the triples mentioned are distinct.) -/
def GPRel {N : ℕ} (ot : ErdosSzekeres.OrderType N) (a b c d e : Fin N) : Prop :=
  let p1 := signMul (ot.σ a b c) (ot.σ a d e)
  let p2 := !(signMul (ot.σ a b d) (ot.σ a c e))
  let p3 := signMul (ot.σ a b e) (ot.σ a c d)
  ¬ (p1 = p2 ∧ p2 = p3)

/-- The oriented-matroid/chirotope axiom scheme (rank 3, uniform case via
    “distinct triple” premises). -/
def IsChirotope {N : ℕ} (ot : ErdosSzekeres.OrderType N) : Prop :=
  ∀ a b c d e : Fin N,
    Distinct3 a b c →
    Distinct3 a d e →
    Distinct3 a b d →
    Distinct3 a c e →
    Distinct3 a b e →
    Distinct3 a c d →
    GPRel ot a b c d e

/-- Acyclicity axiom (rank-3): for any 4 distinct indices, the clause
    ¬σ(a,b,c) ∨ σ(d,b,c) ∨ σ(a,d,c) ∨ σ(a,b,d) holds. -/
def Acyclic {N : ℕ} (ot : ErdosSzekeres.OrderType N) : Prop :=
  ∀ a b c d : Fin N,
    Distinct4 a b c d →
      (ot.σ a b c = false) ∨
      (ot.σ d b c = true) ∨
      (ot.σ a d c = true) ∨
      (ot.σ a b d = true)

/-- `Distinct3` is preserved by reindexing. -/
lemma Distinct3.map {N M : ℕ} (f : Fin N ↪ Fin M) {i j k : Fin N} :
    Distinct3 i j k → Distinct3 (f i) (f j) (f k) := by
  rintro ⟨hij, hik, hjk⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hij (f.injective h)
  · intro h; exact hik (f.injective h)
  · intro h; exact hjk (f.injective h)

/-- The chirotope axiom scheme is preserved under reindexing. -/
lemma IsChirotope.reindex {N M : ℕ} {ot : ErdosSzekeres.OrderType M}
    (h : IsChirotope ot) (f : Fin N ↪ Fin M) :
    IsChirotope (ErdosSzekeres.OrderType.reindex ot f) := by
  intro a b c d e habc hade habd hace habe hacd
  have habc' : Distinct3 (f a) (f b) (f c) := Distinct3.map f habc
  have hade' : Distinct3 (f a) (f d) (f e) := Distinct3.map f hade
  have habd' : Distinct3 (f a) (f b) (f d) := Distinct3.map f habd
  have hace' : Distinct3 (f a) (f c) (f e) := Distinct3.map f hace
  have habe' : Distinct3 (f a) (f b) (f e) := Distinct3.map f habe
  have hacd' : Distinct3 (f a) (f c) (f d) := Distinct3.map f hacd
  have hGP :=
    h (f a) (f b) (f c) (f d) (f e) habc' hade' habd' hace' habe' hacd'
  simpa [GPRel, signMul, ErdosSzekeres.OrderType.reindex] using hGP

/-- A “SAT-search target”: a rank-3 chirotope on `N` elements that avoids an
    alternating `n`-subset. (If this exists, it’s a candidate counterexample at
    the oriented-matroid level.) -/
def OM3Counterexample (n N : ℕ) : Prop :=
  ∃ ot : ErdosSzekeres.OrderType N, IsChirotope ot ∧ AvoidsAlternating ot n

/-- Avoiding alternating subsets is preserved under reindexing (restriction to a
    subset of indices). -/
lemma AvoidsAlternating.reindex {n N M : ℕ} {ot : ErdosSzekeres.OrderType M}
    (h : AvoidsAlternating (ot := ot) n) (f : Fin N ↪ Fin M) :
    AvoidsAlternating (ot := ErdosSzekeres.OrderType.reindex ot f) n := by
  intro g hg
  have hc : ContainsAlternating (ot := ErdosSzekeres.OrderType.reindex ot f) n :=
    ⟨g, hg⟩
  have hc' : ContainsAlternating (ot := ot) n :=
    ContainsAlternating.of_reindex (n := n) (f := f) hc
  exact ((AvoidsAlternating_iff_not_contains (ot := ot) n).1 h) hc'

/-- If a chirotope counterexample exists on `N'` points, then one exists on any smaller `N`. -/
lemma OM3Counterexample.mono {n N N' : ℕ} (hNN' : N ≤ N') :
    OM3Counterexample n N' → OM3Counterexample n N := by
  rintro ⟨ot, hot, havoid⟩
  let f : Fin N ↪ Fin N' := Fin.castLEEmb hNN'
  refine ⟨ErdosSzekeres.OrderType.reindex ot f, ?_, ?_⟩
  · exact IsChirotope.reindex (ot := ot) hot f
  · exact AvoidsAlternating.reindex (ot := ot) (n := n) havoid f

end OrderType

end ErdosSzekeres
