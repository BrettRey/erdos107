import Std
import Erdos107.SATCNF

open ErdosSzekeres
open ErdosSzekeres.SATCNF

namespace ErdosSzekeres

def litVar {N : ℕ} : Lit (Var N) → Var N
  | Lit.pos v => v
  | Lit.neg v => v

def varsOfClause {N : ℕ} (cl : List (Lit (Var N))) : List (Var N) :=
  cl.map litVar

def varsOfCNF {N : ℕ} (cnf : CNF (Var N)) : List (Var N) :=
  cnf.clauses.bind varsOfClause

def varList {N : ℕ} (cnf : CNF (Var N)) : List (Var N) :=
  (varsOfCNF cnf).eraseDups

def varIndex {N : ℕ} (vars : List (Var N)) (v : Var N) : Nat :=
  vars.indexOf v + 1

def litToInt {N : ℕ} (vars : List (Var N)) : Lit (Var N) → Int
  | Lit.pos v => Int.ofNat (varIndex vars v)
  | Lit.neg v => Int.negOfNat (varIndex vars v)

def renderVar {N : ℕ} : Var N → String
  | Var.sigma a b c => s!"sigma {a.val} {b.val} {c.val}"
  | Var.gp1 a b c d e => s!"gp1 {a.val} {b.val} {c.val} {d.val} {e.val}"
  | Var.gp2 a b c d e => s!"gp2 {a.val} {b.val} {c.val} {d.val} {e.val}"
  | Var.gp3 a b c d e => s!"gp3 {a.val} {b.val} {c.val} {d.val} {e.val}"

def writeDimacs {N : ℕ} (path : System.FilePath) (cnf : CNF (Var N)) : IO Unit := do
  let vars := varList cnf
  let numVars := vars.length
  let numClauses := cnf.clauses.length
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  h.putStrLn s!"p cnf {numVars} {numClauses}"
  for cl in cnf.clauses do
    let lits := cl.map (fun lit => (litToInt vars lit).toString)
    h.putStrLn (String.intercalate " " lits ++ " 0")
  h.flush
  h.close

def writeVarMap {N : ℕ} (path : System.FilePath) (cnf : CNF (Var N)) : IO Unit := do
  let vars := varList cnf
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for v in vars do
    let idx := varIndex vars v
    h.putStrLn s!"{idx} {renderVar v}"
  h.flush
  h.close

def usage : String :=
  "usage: emit_cnf <n> <N> <out.cnf> [map.txt]"

def parseNat (s : String) : Option Nat :=
  s.toNat?

def main : IO Unit := do
  let args ← IO.getArgs
  match args with
  | [nStr, NStr, outPath] =>
      match parseNat nStr, parseNat NStr with
      | some n, some N =>
          let blocked : List (Fin n ↪ Fin N) := []
          let cnf := satSpecCNF n N blocked
          writeDimacs outPath cnf
      | _, _ =>
          IO.eprintln usage
          IO.exit 1
  | [nStr, NStr, outPath, mapPath] =>
      match parseNat nStr, parseNat NStr with
      | some n, some N =>
          let blocked : List (Fin n ↪ Fin N) := []
          let cnf := satSpecCNF n N blocked
          writeDimacs outPath cnf
          writeVarMap mapPath cnf
      | _, _ =>
          IO.eprintln usage
          IO.exit 1
  | _ =>
      IO.eprintln usage
      IO.exit 1

end ErdosSzekeres
