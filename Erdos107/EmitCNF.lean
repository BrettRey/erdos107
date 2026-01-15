import Std
import Mathlib.Data.List.Nodup
import Erdos107.SATCNF

open ErdosSzekeres
open ErdosSzekeres.SATCNF

namespace ErdosSzekeres

def litVar {N : ℕ} : Lit (Var N) → Var N
  | Lit.pos v => v
  | Lit.neg v => v

def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

def indexOf {α : Type} [DecidableEq α] : List α → α → Nat
  | [], _ => 0
  | x :: xs, a => if x = a then 0 else indexOf xs a + 1

def varsOfClause {N : ℕ} (cl : List (Lit (Var N))) : List (Var N) :=
  cl.map litVar

def varsOfCNF {N : ℕ} (cnf : CNF (Var N)) : List (Var N) :=
  listBind cnf.clauses varsOfClause

def varList {N : ℕ} (cnf : CNF (Var N)) : List (Var N) :=
  (varsOfCNF cnf).eraseDups

def varIndex {N : ℕ} (vars : List (Var N)) (v : Var N) : Nat :=
  indexOf vars v + 1

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
  IO.FS.withFile path IO.FS.Mode.write fun h => do
    h.putStrLn s!"p cnf {numVars} {numClauses}"
    for cl in cnf.clauses do
      let lits := cl.map (fun lit => toString (litToInt vars lit))
      h.putStrLn (String.intercalate " " lits ++ " 0")

def writeVarMap {N : ℕ} (path : System.FilePath) (cnf : CNF (Var N)) : IO Unit := do
  let vars := varList cnf
  IO.FS.withFile path IO.FS.Mode.write fun h => do
    for v in vars do
      let idx := varIndex vars v
      h.putStrLn s!"{idx} {renderVar v}"

def usage : String :=
  "usage: emit_cnf <n> <N> <out.cnf> [map.txt] [blocked.txt]"

def parseNat (s : String) : Option Nat :=
  s.toNat?

def words (s : String) : List String :=
  (s.splitToList (fun c => c = ' ' || c = '\t')).filter (fun w => w != "")

def natToFin (N : Nat) (m : Nat) : Except String (Fin N) := do
  if h : m < N then
    return ⟨m, h⟩
  else
    throw s!"index {m} out of range (>= {N})"

def parseFins' (N : Nat) : (xs : List Nat) → Except String {ys : List (Fin N) // ys.length = xs.length}
  | [] => return ⟨[], rfl⟩
  | m :: ms => do
      let f ← natToFin N m
      let ⟨rest, hrest⟩ ← parseFins' N ms
      return ⟨f :: rest, by simpa [hrest]⟩

def embeddingOfList {N n : Nat} (xs : List (Fin N)) (hlen : xs.length = n)
    (hnodup : xs.Nodup) : Fin n ↪ Fin N :=
  let idx : Fin n → Fin xs.length := fun i =>
    ⟨i.val, by simpa [hlen] using i.is_lt⟩
  ⟨fun i => xs.get (idx i),
   by
     intro i j hij
     have hinj : Function.Injective xs.get := (List.nodup_iff_injective_get).1 hnodup
     have hidx : idx i = idx j := by
       apply hinj
       simpa using hij
     apply Fin.ext
     simpa using congrArg Fin.val hidx⟩

def parseLine {n N : Nat} (line : String) : Except String (Fin n ↪ Fin N) := do
  let ws := words line
  if ws.isEmpty then
    throw "empty line"
  let nums? := ws.map parseNat
  if nums?.any (fun o => o.isNone) then
    throw "non-numeric token"
  let nums : List Nat := nums?.map Option.get!
  if hlen : nums.length = n then
    let ⟨fins, hlenF⟩ ← parseFins' N nums
    if hnodup : fins.Nodup then
      have hlenF' : fins.length = n := by
        simpa [hlen] using hlenF
      return embeddingOfList fins hlenF' hnodup
    else
      throw "duplicate index in line"
  else
    throw s!"expected {n} numbers, got {nums.length}"

def loadBlocked (n N : Nat) (path : System.FilePath) : IO (List (Fin n ↪ Fin N)) := do
  let content ← IO.FS.readFile path
  let lines := content.splitToList (fun c => c = '\n')
  let mut acc : List (Fin n ↪ Fin N) := []
  for line in lines do
    let t := line.trim
    if t.isEmpty || t.startsWith "#" then
      continue
    match parseLine (n := n) (N := N) t with
    | Except.ok e => acc := e :: acc
    | Except.error msg =>
        throw <| IO.userError s!"blocked.txt parse error: {msg} | line: {t}"
  return acc.reverse

def die : IO Unit := do
  IO.eprintln usage
  throw <| IO.userError "bad arguments"

def emitMain (args : List String) : IO Unit := do
  match args with
  | [nStr, NStr, outPath] =>
      match parseNat nStr, parseNat NStr with
      | some n, some N =>
          let blocked : List (Fin n ↪ Fin N) := []
          let cnf := satSpecCNF n N blocked
          writeDimacs outPath cnf
      | _, _ =>
          die
  | [nStr, NStr, outPath, mapPath] =>
      match parseNat nStr, parseNat NStr with
      | some n, some N =>
          let blocked : List (Fin n ↪ Fin N) := []
          let cnf := satSpecCNF n N blocked
          writeDimacs outPath cnf
          writeVarMap mapPath cnf
      | _, _ =>
          die
  | [nStr, NStr, outPath, mapPath, blockedPath] =>
      match parseNat nStr, parseNat NStr with
      | some n, some N =>
          let blocked ← loadBlocked n N blockedPath
          let cnf := satSpecCNF n N blocked
          writeDimacs outPath cnf
          writeVarMap mapPath cnf
      | _, _ =>
          die
  | _ =>
      die

end ErdosSzekeres

def main (args : List String) : IO Unit :=
  ErdosSzekeres.emitMain args
