import Erdos107.SATSpec
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.List.Basic

namespace ErdosSzekeres

inductive Lit (Var : Type)
  | pos : Var → Lit Var
  | neg : Var → Lit Var

structure CNF (Var : Type) where
  clauses : List (List (Lit Var))

/-- A valuation assigns truth values to variables. -/
def Valuation (Var : Type) : Type := Var → Bool

def evalLit {Var : Type} (v : Valuation Var) : Lit Var → Bool
  | Lit.pos x => v x
  | Lit.neg x => !v x

def evalClause {Var : Type} (v : Valuation Var) (cl : List (Lit Var)) : Bool :=
  cl.any (fun x => evalLit v x)

def evalCNF {Var : Type} (v : Valuation Var) (cnf : CNF Var) : Bool :=
  cnf.clauses.all (fun cl => evalClause v cl)

lemma evalClause_two {Var : Type} (v : Valuation Var) (l₁ l₂ : Lit Var) :
    evalClause v [l₁, l₂] = (evalLit v l₁ || evalLit v l₂) := by
  simp [evalClause]

lemma evalClause_four {Var : Type} (v : Valuation Var) (l₁ l₂ l₃ l₄ : Lit Var) :
    evalClause v [l₁, l₂, l₃, l₄] =
      (evalLit v l₁ || (evalLit v l₂ || (evalLit v l₃ || evalLit v l₄))) := by
  simp [evalClause]

lemma evalCNF_cons {Var : Type} (v : Valuation Var) (cl : List (Lit Var))
    (cls : List (List (Lit Var))) :
    evalCNF v { clauses := cl :: cls } =
      (evalClause v cl && evalCNF v { clauses := cls }) := by
  simp [evalCNF]

lemma evalCNF_nil {Var : Type} (v : Valuation Var) :
    evalCNF v { clauses := [] } = true := by
  simp [evalCNF]

lemma evalCNF_append {Var : Type} (v : Valuation Var) (c1 c2 : CNF Var) :
    evalCNF v { clauses := c1.clauses ++ c2.clauses } =
      (evalCNF v c1 && evalCNF v c2) := by
  simp [evalCNF, List.all_append]

def Satisfiable {Var : Type} (cnf : CNF Var) : Prop :=
  ∃ v : Valuation Var, evalCNF v cnf = true

namespace SATCNF

inductive Var (N : ℕ)
  | sigma (a b c : Fin N)
  | gp1 (a b c d e : Fin N)
  | gp2 (a b c d e : Fin N)
  | gp3 (a b c d e : Fin N)

def valuationOfOrderType {N : ℕ} (ot : OrderType N) : Valuation (Var N)
  | Var.sigma a b c => ot.σ a b c
  | Var.gp1 a b c d e => decide (ot.σ a b c = ot.σ a d e)
  | Var.gp2 a b c d e => decide (ot.σ a b d = ot.σ a c e)
  | Var.gp3 a b c d e => decide (ot.σ a b e = ot.σ a c d)

def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

lemma mem_listBind {α β : Type} {xs : List α} {f : α → List β} {y : β} :
    y ∈ listBind xs f ↔ ∃ x ∈ xs, y ∈ f x := by
  induction xs with
  | nil =>
      simp [listBind]
  | cons x xs ih =>
      simp [listBind, ih, List.mem_append, or_left_comm, or_assoc, exists_or, and_left_comm,
        and_assoc]

def allFin (N : ℕ) : List (Fin N) :=
  List.ofFn (fun i : Fin N => i)

def Distinct5 {N : ℕ} (a b c d e : Fin N) : Prop :=
  Distinct4 a b c d ∧ a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e

noncomputable def swap12Clauses (N : ℕ) : List (List (Lit (Var N))) := by
  classical
  exact
    listBind (allFin N) fun a =>
      listBind (allFin N) fun b =>
        listBind (allFin N) fun c =>
          if h : Distinct3 a b c then
            let x := Var.sigma a b c
            let y := Var.sigma b a c
            [[Lit.pos x, Lit.pos y], [Lit.neg x, Lit.neg y]]
          else []

noncomputable def cycleClauses (N : ℕ) : List (List (Lit (Var N))) := by
  classical
  exact
    listBind (allFin N) fun a =>
      listBind (allFin N) fun b =>
        listBind (allFin N) fun c =>
          if h : Distinct3 a b c then
            let x := Var.sigma a b c
            let y := Var.sigma b c a
            [[Lit.neg x, Lit.pos y], [Lit.pos x, Lit.neg y]]
          else []

noncomputable def acyclicClauses (N : ℕ) : List (List (Lit (Var N))) := by
  classical
  exact
    listBind (allFin N) fun a =>
      listBind (allFin N) fun b =>
        listBind (allFin N) fun c =>
          listBind (allFin N) fun d =>
            if h : Distinct4 a b c d then
              let x := Var.sigma a b c
              let y := Var.sigma d b c
              let z := Var.sigma a d c
              let w := Var.sigma a b d
              [[Lit.neg x, Lit.pos y, Lit.pos z, Lit.pos w]]
            else []

def xnorClauses {N : ℕ} (q x y : Var N) : List (List (Lit (Var N))) :=
  [ [Lit.pos q, Lit.pos x, Lit.pos y]
  , [Lit.pos q, Lit.neg x, Lit.neg y]
  , [Lit.neg q, Lit.pos x, Lit.neg y]
  , [Lit.neg q, Lit.neg x, Lit.pos y]
  ]

lemma xnorClauses_sound {N : ℕ} (v : Valuation (Var N)) (q x y : Var N)
    (hq : v q = decide (v x = v y)) :
    evalCNF v { clauses := xnorClauses q x y } = true := by
  cases hx : v x <;> cases hy : v y <;>
    simp [xnorClauses, evalCNF, evalClause, evalLit, hq, hx, hy]

noncomputable def gpRelClauses (N : ℕ) : List (List (Lit (Var N))) := by
  classical
  exact
    listBind (allFin N) fun a =>
      listBind (allFin N) fun b =>
        listBind (allFin N) fun c =>
          listBind (allFin N) fun d =>
            listBind (allFin N) fun e =>
              if h : Distinct5 a b c d e then
                let s_abc := Var.sigma a b c
                let s_ade := Var.sigma a d e
                let s_abd := Var.sigma a b d
                let s_ace := Var.sigma a c e
                let s_abe := Var.sigma a b e
                let s_acd := Var.sigma a c d
                let p1 := Var.gp1 a b c d e
                let p2 := Var.gp2 a b c d e
                let p3 := Var.gp3 a b c d e
                xnorClauses p1 s_abc s_ade ++
                xnorClauses p2 s_abd s_ace ++
                xnorClauses p3 s_abe s_acd ++
                [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                , [Lit.neg p1, Lit.pos p2, Lit.neg p3]
                ]
              else []

def triples (n : ℕ) : List (Fin n × Fin n × Fin n) := by
  classical
  exact
    listBind (allFin n) fun i =>
      listBind (allFin n) fun j =>
        listBind (allFin n) fun k =>
          if h : i < j ∧ j < k then
            [(i, j, k)]
          else []

lemma mem_triples_of_lt {n : ℕ} {i j k : Fin n} (h : i < j ∧ j < k) :
    (i, j, k) ∈ triples n := by
  classical
  -- unfold and use mem_listBind repeatedly
  refine (mem_listBind).2 ?_
  refine ⟨i, by simp [allFin], ?_⟩
  refine (mem_listBind).2 ?_
  refine ⟨j, by simp [allFin], ?_⟩
  refine (mem_listBind).2 ?_
  refine ⟨k, by simp [allFin], ?_⟩
  simp [triples, h]

def avoidClause {n N : ℕ} (f : Fin n ↪ Fin N) : List (Lit (Var N)) :=
  (triples n).map (fun t => match t with
    | (i, j, k) => Lit.neg (Var.sigma (f i) (f j) (f k)))

def avoidClauses {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) : List (List (Lit (Var N))) :=
  blocked.map avoidClause

lemma avoidClause_false_iff {n N : ℕ} (ot : OrderType N) (f : Fin n ↪ Fin N) :
    evalClause (valuationOfOrderType ot) (avoidClause f) = false ↔
      ∀ t ∈ triples n,
        match t with
        | (i, j, k) => ot.σ (f i) (f j) (f k) = true := by
  classical
  constructor
  · intro hfalse t ht
    rcases t with ⟨i, j, k⟩
    have hmem : Lit.neg (Var.sigma (f i) (f j) (f k)) ∈ avoidClause f := by
      refine (List.mem_map).2 ?_
      exact ⟨(i, j, k), ht, rfl⟩
    have hfalse' :
        (avoidClause f).any (fun lit => evalLit (valuationOfOrderType ot) lit) = false := by
      simpa [evalClause] using hfalse
    have h := (List.any_eq_false).1 hfalse' _ hmem
    have h' : (!ot.σ (f i) (f j) (f k)) = false := by
      simpa [evalLit, valuationOfOrderType] using h
    cases hσ : ot.σ (f i) (f j) (f k) with
    | false =>
        have : False := by
          simpa [hσ] using h'
        exact this.elim
    | true =>
        exact hσ
  · intro hall
    have hfalse' :
        (avoidClause f).any (fun lit => evalLit (valuationOfOrderType ot) lit) = false := by
      apply (List.any_eq_false).2
      intro lit hlit
      rcases (List.mem_map).1 hlit with ⟨t, ht, rfl⟩
      rcases t with ⟨i, j, k⟩
      specialize hall (i, j, k) ht
      simpa [evalLit, valuationOfOrderType, hall]
    simpa [evalClause] using hfalse'

noncomputable def satSpecCNF (n N : ℕ) (blocked : List (Fin n ↪ Fin N)) : CNF (Var N) := by
  classical
  exact {
    clauses :=
      swap12Clauses N ++ cycleClauses N ++ acyclicClauses N ++ gpRelClauses N ++
        avoidClauses blocked
  }

lemma swap12_clause_pos {N : ℕ} (ot : OrderType N) {a b c : Fin N}
    (h : Distinct3 a b c) :
    evalClause (valuationOfOrderType ot)
      [Lit.pos (Var.sigma a b c), Lit.pos (Var.sigma b a c)] = true := by
  have hs : ot.σ a b c = !ot.σ b a c := ot.swap12 h
  cases hbc : ot.σ b a c <;> simp [evalClause_two, valuationOfOrderType, evalLit, hs, hbc]

lemma swap12_clause_neg {N : ℕ} (ot : OrderType N) {a b c : Fin N}
    (h : Distinct3 a b c) :
    evalClause (valuationOfOrderType ot)
      [Lit.neg (Var.sigma a b c), Lit.neg (Var.sigma b a c)] = true := by
  have hs : ot.σ a b c = !ot.σ b a c := ot.swap12 h
  cases hbc : ot.σ b a c <;> simp [evalClause_two, valuationOfOrderType, evalLit, hs, hbc]

lemma cycle_clause_pos {N : ℕ} (ot : OrderType N) {a b c : Fin N}
    (h : Distinct3 a b c) :
    evalClause (valuationOfOrderType ot)
      [Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma b c a)] = true := by
  have hc : ot.σ a b c = ot.σ b c a := ot.cycle h
  cases hbc : ot.σ a b c <;> simp [evalClause_two, valuationOfOrderType, evalLit, hc, hbc]

lemma cycle_clause_neg {N : ℕ} (ot : OrderType N) {a b c : Fin N}
    (h : Distinct3 a b c) :
    evalClause (valuationOfOrderType ot)
      [Lit.pos (Var.sigma a b c), Lit.neg (Var.sigma b c a)] = true := by
  have hc : ot.σ a b c = ot.σ b c a := ot.cycle h
  cases hbc : ot.σ a b c <;> simp [evalClause_two, valuationOfOrderType, evalLit, hc, hbc]

lemma acyclic_clause {N : ℕ} (ot : OrderType N) (hacyc : OrderType.Acyclic ot)
    {a b c d : Fin N} (h : Distinct4 a b c d) :
    evalClause (valuationOfOrderType ot)
      [Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma d b c),
       Lit.pos (Var.sigma a d c), Lit.pos (Var.sigma a b d)] = true := by
  have hacyc' := hacyc a b c d h
  rcases hacyc' with h1 | hrest
  · simp [evalClause_four, valuationOfOrderType, evalLit, h1]
  · rcases hrest with h2 | hrest
    · simp [evalClause_four, valuationOfOrderType, evalLit, h2]
    · rcases hrest with h3 | h4
      · simp [evalClause_four, valuationOfOrderType, evalLit, h3]
      · simp [evalClause_four, valuationOfOrderType, evalLit, h4]

theorem swap12Clauses_sound {N : ℕ} (ot : OrderType N) :
    evalCNF (valuationOfOrderType ot) { clauses := swap12Clauses N } = true := by
  classical
  -- Show all clauses generated by swap12 are satisfied.
  apply (List.all_eq_true).2
  intro cl hcl
  -- Unpack listBind membership.
  rcases (mem_listBind.mp hcl) with ⟨a, ha, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨b, hb, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨c, hc, hcl⟩
  by_cases h : Distinct3 a b c
  · have hcl' : cl ∈
        [[Lit.pos (Var.sigma a b c), Lit.pos (Var.sigma b a c)],
         [Lit.neg (Var.sigma a b c), Lit.neg (Var.sigma b a c)]] := by
        simpa [h] using hcl
    -- cl is one of the two swap12 clauses
    have hcl'' :
        cl =
            [Lit.pos (Var.sigma a b c), Lit.pos (Var.sigma b a c)] ∨
          cl =
            [Lit.neg (Var.sigma a b c), Lit.neg (Var.sigma b a c)] := by
      simpa using hcl'
    rcases hcl'' with hcl'' | hcl''
    · simpa [hcl''] using swap12_clause_pos ot h
    · simpa [hcl''] using swap12_clause_neg ot h
  · have : False := by
      simpa [h] using hcl
    exact this.elim

theorem cycleClauses_sound {N : ℕ} (ot : OrderType N) :
    evalCNF (valuationOfOrderType ot) { clauses := cycleClauses N } = true := by
  classical
  apply (List.all_eq_true).2
  intro cl hcl
  rcases (mem_listBind.mp hcl) with ⟨a, ha, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨b, hb, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨c, hc, hcl⟩
  by_cases h : Distinct3 a b c
  · have hcl' : cl ∈
        [[Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma b c a)],
         [Lit.pos (Var.sigma a b c), Lit.neg (Var.sigma b c a)]] := by
        simpa [h] using hcl
    have hcl'' :
        cl =
            [Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma b c a)] ∨
          cl =
            [Lit.pos (Var.sigma a b c), Lit.neg (Var.sigma b c a)] := by
      simpa using hcl'
    rcases hcl'' with hcl'' | hcl''
    · simpa [hcl''] using cycle_clause_pos ot h
    · simpa [hcl''] using cycle_clause_neg ot h
  · have : False := by
      simpa [h] using hcl
    exact this.elim

theorem acyclicClauses_sound {N : ℕ} (ot : OrderType N) (h : OrderType.Acyclic ot) :
    evalCNF (valuationOfOrderType ot) { clauses := acyclicClauses N } = true := by
  classical
  apply (List.all_eq_true).2
  intro cl hcl
  rcases (mem_listBind.mp hcl) with ⟨a, ha, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨b, hb, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨c, hc, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨d, hd, hcl⟩
  by_cases h' : Distinct4 a b c d
  · have hcl' : cl ∈
        [[Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma d b c),
          Lit.pos (Var.sigma a d c), Lit.pos (Var.sigma a b d)]] := by
        simpa [h'] using hcl
    have hcl'' :
        cl =
          [Lit.neg (Var.sigma a b c), Lit.pos (Var.sigma d b c),
           Lit.pos (Var.sigma a d c), Lit.pos (Var.sigma a b d)] := by
      simpa using hcl'
    simpa [hcl''] using acyclic_clause ot h h'
  · have : False := by
      simpa [h'] using hcl
    exact this.elim

theorem gpRelClauses_sound {N : ℕ} (ot : OrderType N) (h : OrderType.IsChirotope ot) :
    evalCNF (valuationOfOrderType ot) { clauses := gpRelClauses N } = true := by
  classical
  apply (List.all_eq_true).2
  intro cl hcl
  rcases (mem_listBind.mp hcl) with ⟨a, ha, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨b, hb, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨c, hc, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨d, hd, hcl⟩
  rcases (mem_listBind.mp hcl) with ⟨e, he, hcl⟩
  by_cases h' : Distinct5 a b c d e
  · have hcl' : cl ∈
        (let s_abc := Var.sigma a b c
         let s_ade := Var.sigma a d e
         let s_abd := Var.sigma a b d
         let s_ace := Var.sigma a c e
         let s_abe := Var.sigma a b e
         let s_acd := Var.sigma a c d
         let p1 := Var.gp1 a b c d e
         let p2 := Var.gp2 a b c d e
         let p3 := Var.gp3 a b c d e
         xnorClauses p1 s_abc s_ade ++
         xnorClauses p2 s_abd s_ace ++
         xnorClauses p3 s_abe s_acd ++
         [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
         , [Lit.neg p1, Lit.pos p2, Lit.neg p3]
         ]) := by
        simpa [h'] using hcl
    -- show all clauses in this chunk evaluate to true
    let v := valuationOfOrderType ot
    let s_abc := Var.sigma a b c
    let s_ade := Var.sigma a d e
    let s_abd := Var.sigma a b d
    let s_ace := Var.sigma a c e
    let s_abe := Var.sigma a b e
    let s_acd := Var.sigma a c d
    let p1 := Var.gp1 a b c d e
    let p2 := Var.gp2 a b c d e
    let p3 := Var.gp3 a b c d e
    have h1 : evalCNF v { clauses := xnorClauses p1 s_abc s_ade } = true := by
      apply xnorClauses_sound v p1 s_abc s_ade
      rfl
    have h2 : evalCNF v { clauses := xnorClauses p2 s_abd s_ace } = true := by
      apply xnorClauses_sound v p2 s_abd s_ace
      rfl
    have h3 : evalCNF v { clauses := xnorClauses p3 s_abe s_acd } = true := by
      apply xnorClauses_sound v p3 s_abe s_acd
      rfl
    -- use chirotope axiom for NAE clauses
    rcases h' with ⟨h4, hae, hbe, hce, hde⟩
    rcases h4 with ⟨hab, hac, had, hbc, hbd, hcd⟩
    have habc : Distinct3 a b c := ⟨hab, hac, hbc⟩
    have hade : Distinct3 a d e := ⟨had, hae, hde⟩
    have habd : Distinct3 a b d := ⟨hab, had, hbd⟩
    have hace : Distinct3 a c e := ⟨hac, hae, hce⟩
    have habe : Distinct3 a b e := ⟨hab, hae, hbe⟩
    have hacd : Distinct3 a c d := ⟨hac, had, hcd⟩
    have hGP := h a b c d e habc hade habd hace habe hacd
    let q1 := decide (ot.σ a b c = ot.σ a d e)
    let q2 := decide (ot.σ a b d = ot.σ a c e)
    let q3 := decide (ot.σ a b e = ot.σ a c d)
    have hGP' : ¬ (q1 = (!q2) ∧ (!q2) = q3) := by
      simpa [OrderType.GPRel, OrderType.signMul, q1, q2, q3] using hGP
    have hv1 : v p1 = q1 := rfl
    have hv2 : v p2 = q2 := rfl
    have hv3 : v p3 = q3 := rfl
    have hcl1 : evalClause v [Lit.pos p1, Lit.neg p2, Lit.pos p3] = true := by
      -- evaluates to q1 || !q2 || q3
      by_cases h1' : q1
      · by_cases h2' : q2
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
      · by_cases h2' : q2
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · -- q1 = false, q2 = true, q3 = false contradicts GPRel
            have : False := by
              have : q1 = (!q2) ∧ (!q2) = q3 := by
                simp [h1', h2', h3']
              exact hGP' this
            exact this.elim
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
    have hcl2 : evalClause v [Lit.neg p1, Lit.pos p2, Lit.neg p3] = true := by
      -- evaluates to !q1 || q2 || !q3
      by_cases h1' : q1
      · by_cases h2' : q2
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
        · by_cases h3' : q3
          · -- q1 = true, q2 = false, q3 = true contradicts GPRel
            have : False := by
              have : q1 = (!q2) ∧ (!q2) = q3 := by
                simp [h1', h2', h3']
              exact hGP' this
            exact this.elim
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
      · by_cases h2' : q2
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
        · by_cases h3' : q3
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
          · simp [evalClause, evalLit, hv1, hv2, hv3, h1', h2', h3']
    have h4 : evalCNF v { clauses := [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                                     , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] } = true := by
      simp [evalCNF, hcl1, hcl2]
    have hchunk :
        evalCNF v { clauses :=
          xnorClauses p1 s_abc s_ade ++
            (xnorClauses p2 s_abd s_ace ++
              (xnorClauses p3 s_abe s_acd ++
                [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ])) } = true := by
      have h12 :
          evalCNF v { clauses :=
            xnorClauses p1 s_abc s_ade ++
              (xnorClauses p2 s_abd s_ace ++
                (xnorClauses p3 s_abe s_acd ++
                  [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                  , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ])) } =
            (evalCNF v { clauses := xnorClauses p1 s_abc s_ade } &&
             evalCNF v { clauses :=
               xnorClauses p2 s_abd s_ace ++
                 (xnorClauses p3 s_abe s_acd ++
                   [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                   , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ]) }) := by
        simpa using
          (evalCNF_append (v := v)
            (c1 := { clauses := xnorClauses p1 s_abc s_ade })
            (c2 := { clauses :=
              xnorClauses p2 s_abd s_ace ++
                (xnorClauses p3 s_abe s_acd ++
                  [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                  , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ]) }))
      have h23 :
          evalCNF v { clauses :=
            xnorClauses p2 s_abd s_ace ++
              (xnorClauses p3 s_abe s_acd ++
                [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ]) } =
            (evalCNF v { clauses := xnorClauses p2 s_abd s_ace } &&
             evalCNF v { clauses :=
               xnorClauses p3 s_abe s_acd ++
                 [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                 , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] }) := by
        simpa using
          (evalCNF_append (v := v)
            (c1 := { clauses := xnorClauses p2 s_abd s_ace })
            (c2 := { clauses :=
              xnorClauses p3 s_abe s_acd ++
                [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
                , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] }))
      have h34 :
          evalCNF v { clauses :=
            xnorClauses p3 s_abe s_acd ++
              [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
              , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] } =
            (evalCNF v { clauses := xnorClauses p3 s_abe s_acd } &&
             evalCNF v { clauses :=
               [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
               , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] }) := by
        simpa using
          (evalCNF_append (v := v)
            (c1 := { clauses := xnorClauses p3 s_abe s_acd })
            (c2 := { clauses :=
              [ [Lit.pos p1, Lit.neg p2, Lit.pos p3]
              , [Lit.neg p1, Lit.pos p2, Lit.neg p3] ] }))
      simp [h12, h23, h34, h1, h2, h3, h4]
    exact (List.all_eq_true).1 hchunk cl hcl'
  · have : False := by
      simpa [h'] using hcl
    exact this.elim

theorem avoidClause_sound {n N : ℕ} (ot : OrderType N)
    (h : OrderType.AvoidsAlternating ot n) (f : Fin n ↪ Fin N) :
    evalClause (valuationOfOrderType ot) (avoidClause f) = true := by
  classical
  by_contra hfalse
  cases hval : evalClause (valuationOfOrderType ot) (avoidClause f) with
  | true =>
      exact (hfalse (by simpa [hval])).elim
  | false =>
      have hall := (avoidClause_false_iff ot f).1 (by simpa [hval])
      -- continue below
      let ot' : OrderType n := OrderType.reindex ot f
      have hcyc_true : ∀ {i j k : Fin n}, OrderType.CyclicTriple i j k → ot'.σ i j k = true := by
        intro i j k hcyc
        rcases hcyc with h1 | h2 | h3
        · -- i < j < k
          have ht := hall (i, j, k) (mem_triples_of_lt h1)
          simpa [OrderType.reindex] using ht
        · -- j < k < i
          have ht := hall (j, k, i) (mem_triples_of_lt h2)
          have hij : i ≠ j := by
            have hji_val : (j : ℕ) < i := Nat.lt_trans
              ((Fin.lt_def).1 h2.1)
              ((Fin.lt_def).1 h2.2)
            have hne : (j : ℕ) ≠ i := ne_of_lt hji_val
            exact ne_comm.mp ((Fin.ne_iff_vne _ _).2 hne)
          have hik : i ≠ k := by
            have hki_val : (k : ℕ) < i := (Fin.lt_def).1 h2.2
            have hne : (k : ℕ) ≠ i := ne_of_lt hki_val
            exact ne_comm.mp ((Fin.ne_iff_vne _ _).2 hne)
          have hjk : j ≠ k := by
            have hjk_val : (j : ℕ) < k := (Fin.lt_def).1 h2.1
            exact (Fin.ne_iff_vne _ _).2 (ne_of_lt hjk_val)
          have hdist : Distinct3 i j k := ⟨hij, hik, hjk⟩
          have hcycle : ot'.σ i j k = ot'.σ j k i := ot'.cycle hdist
          simpa [OrderType.reindex, hcycle] using ht
        · -- k < i < j
          have ht := hall (k, i, j) (mem_triples_of_lt h3)
          have hij : i ≠ j := by
            have hij_val : (i : ℕ) < j := (Fin.lt_def).1 h3.2
            exact (Fin.ne_iff_vne _ _).2 (ne_of_lt hij_val)
          have hik : i ≠ k := by
            have hki_val : (k : ℕ) < i := (Fin.lt_def).1 h3.1
            exact ne_comm.mp ((Fin.ne_iff_vne _ _).2 (ne_of_lt hki_val))
          have hjk : j ≠ k := by
            have hkj_val : (k : ℕ) < j := Nat.lt_trans
              ((Fin.lt_def).1 h3.1)
              ((Fin.lt_def).1 h3.2)
            exact ne_comm.mp ((Fin.ne_iff_vne _ _).2 (ne_of_lt hkj_val))
          have hdist : Distinct3 i j k := ⟨hij, hik, hjk⟩
          have hdist' : Distinct3 j k i := ⟨hjk, ne_comm.mp hij, ne_comm.mp hik⟩
          have hcycle1 : ot'.σ i j k = ot'.σ j k i := ot'.cycle hdist
          have hcycle2 : ot'.σ j k i = ot'.σ k i j := ot'.cycle hdist'
          -- chain the cycles and use ht
          simpa [OrderType.reindex, hcycle1, hcycle2] using ht
      -- show ot' is alternating, contradicting AvoidsAlternating
      have hAlt : OrderType.IsAlternating ot' := by
        intro i j k hdist
        by_cases hcyc : OrderType.CyclicTriple i j k
        · have ht := hcyc_true (i := i) (j := j) (k := k) hcyc
          simp [OrderType.altσ, hcyc, ht]
        · -- non-cyclic: swap first two yields cyclic
          have hswapcyc : OrderType.CyclicTriple j i k := by
            -- case split on the total order of i,j,k
            have hij' : (i : ℕ) < j ∨ (j : ℕ) < i :=
              lt_or_gt_of_ne ((Fin.ne_iff_vne _ _).1 hdist.1)
            have hik' : (i : ℕ) < k ∨ (k : ℕ) < i :=
              lt_or_gt_of_ne ((Fin.ne_iff_vne _ _).1 hdist.2.1)
            have hjk' : (j : ℕ) < k ∨ (k : ℕ) < j :=
              lt_or_gt_of_ne ((Fin.ne_iff_vne _ _).1 hdist.2.2)
            have hij : i < j ∨ j < i := by
              cases hij' with
              | inl h => exact Or.inl ((Fin.lt_def).2 h)
              | inr h => exact Or.inr ((Fin.lt_def).2 h)
            have hik : i < k ∨ k < i := by
              cases hik' with
              | inl h => exact Or.inl ((Fin.lt_def).2 h)
              | inr h => exact Or.inr ((Fin.lt_def).2 h)
            have hjk : j < k ∨ k < j := by
              cases hjk' with
              | inl h => exact Or.inl ((Fin.lt_def).2 h)
              | inr h => exact Or.inr ((Fin.lt_def).2 h)
            cases hij with
            | inl hij =>
                cases hjk with
                | inl hjk =>
                    -- i<j<k would make cyclic, contradiction
                    exact (hcyc (Or.inl ⟨hij, hjk⟩)).elim
                | inr hkj =>
                    cases hik with
                    | inl hik =>
                        -- i<k<j -> cyclic for j i k (second disjunct)
                        exact Or.inr (Or.inl ⟨hik, hkj⟩)
                    | inr hki =>
                        -- k<i<j would make cyclic, contradiction
                        exact (hcyc (Or.inr (Or.inr ⟨hki, hij⟩))).elim
            | inr hji =>
                cases hik with
                | inl hik =>
                    -- j<i<k -> cyclic for j i k (first disjunct)
                    exact Or.inl ⟨hji, hik⟩
                | inr hki =>
                    cases hjk with
                    | inl hjk =>
                        -- j<k<i would make cyclic, contradiction
                        exact (hcyc (Or.inr (Or.inl ⟨hjk, hki⟩))).elim
                    | inr hkj =>
                        -- k<j<i -> cyclic for j i k (third disjunct)
                        exact Or.inr (Or.inr ⟨hkj, hji⟩)
          have ht := hcyc_true (i := j) (j := i) (k := k) hswapcyc
          have hswap : ot'.σ i j k = ! ot'.σ j i k := ot'.swap12 hdist
          -- altσ is false when cyclicTriple is false
          simp [OrderType.altσ, hcyc, hswap, ht]
      exact (h f) hAlt
theorem satSpecCNF_sound {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) (ot : OrderType N)
    (_h : SATSpec n N ot) :
    Satisfiable (satSpecCNF n N blocked) := by
  -- TODO: prove soundness from SATSpec (swap/cycle/acyclic + GPRel + avoidance).
  classical
  refine ⟨valuationOfOrderType ot, ?_⟩
  -- TODO: combine clause soundness lemmas.
  sorry

theorem satCounterexample_imp_satisfiable {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) :
    SATCounterexample n N → Satisfiable (satSpecCNF n N blocked) := by
  rintro ⟨ot, h⟩
  exact satSpecCNF_sound blocked ot h

end SATCNF

end ErdosSzekeres
