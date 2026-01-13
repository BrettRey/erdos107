import Erdos107.SATSpec
import Mathlib.Data.Fin.Basic

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

def satSpecCNF (n N : ℕ) : CNF (Var N) :=
  { clauses := [] }

def valuationOfOrderType {N : ℕ} (ot : OrderType N) : Valuation (Var N)
  | Var.sigma a b c => ot.σ a b c

theorem satSpecCNF_sound {n N : ℕ} (ot : OrderType N) (h : SATSpec n N ot) :
    Satisfiable (satSpecCNF n N) := by
  -- TODO: populate CNF and prove soundness.
  classical
  refine ⟨valuationOfOrderType ot, ?_⟩
  simp [satSpecCNF, evalCNF, evalClause]

theorem satCounterexample_imp_satisfiable {n N : ℕ} :
    SATCounterexample n N → Satisfiable (satSpecCNF n N) := by
  rintro ⟨ot, h⟩
  exact satSpecCNF_sound ot h

end SATCNF

end ErdosSzekeres
