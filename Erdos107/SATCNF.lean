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

def Satisfiable {Var : Type} (cnf : CNF Var) : Prop :=
  ∃ v : Valuation Var, evalCNF v cnf = true

namespace SATCNF

inductive Var (N : ℕ)
  | sigma (a b c : Fin N)
  | gp1 (a b c d e : Fin N)
  | gp2 (a b c d e : Fin N)
  | gp3 (a b c d e : Fin N)

def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

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

def avoidClause {n N : ℕ} (f : Fin n ↪ Fin N) : List (Lit (Var N)) :=
  (triples n).map (fun t => match t with
    | (i, j, k) => Lit.neg (Var.sigma (f i) (f j) (f k)))

def avoidClauses {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) : List (List (Lit (Var N))) :=
  blocked.map avoidClause

noncomputable def satSpecCNF (n N : ℕ) (blocked : List (Fin n ↪ Fin N)) : CNF (Var N) := by
  classical
  exact {
    clauses :=
      swap12Clauses N ++ cycleClauses N ++ acyclicClauses N ++ gpRelClauses N ++
        avoidClauses blocked
  }

def valuationOfOrderType {N : ℕ} (ot : OrderType N) : Valuation (Var N)
  | Var.sigma a b c => ot.σ a b c
  | Var.gp1 a b c d e => decide (ot.σ a b c = ot.σ a d e)
  | Var.gp2 a b c d e => decide (ot.σ a b d = ot.σ a c e)
  | Var.gp3 a b c d e => decide (ot.σ a b e = ot.σ a c d)

theorem avoidClause_sound {n N : ℕ} (ot : OrderType N)
    (h : OrderType.AvoidsAlternating ot n) (f : Fin n ↪ Fin N) :
    evalClause (valuationOfOrderType ot) (avoidClause f) = true := by
  -- TODO: unfold IsAlternating/avoidClause and show one triple is false.
  classical
  sorry

theorem satSpecCNF_sound {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) (ot : OrderType N)
    (_h : SATSpec n N ot) :
    Satisfiable (satSpecCNF n N blocked) := by
  -- TODO: prove soundness from SATSpec (swap/cycle/acyclic + GPRel + avoidance).
  classical
  sorry

theorem satCounterexample_imp_satisfiable {n N : ℕ} (blocked : List (Fin n ↪ Fin N)) :
    SATCounterexample n N → Satisfiable (satSpecCNF n N blocked) := by
  rintro ⟨ot, h⟩
  exact satSpecCNF_sound blocked ot h

end SATCNF

end ErdosSzekeres
