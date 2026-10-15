/-
  Simple Lean 4 example: definitions, evaluation, and proofs.
  Plain Lean core only (no Mathlib). Zero sorries.
-/

-- A function
def double (n : Nat) : Nat := n + n

#eval double 21  -- 42

-- Proof by computation
theorem double_two : double 2 = 4 := rfl

-- Proof with a tactic: unfold the definition, let `omega` do arithmetic
theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double
  omega

-- A recursive function on lists
def myLength {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + myLength xs

#eval myLength [10, 20, 30]  -- 3

-- Proof by induction
theorem myLength_append {α : Type} (xs ys : List α) :
    myLength (xs ++ ys) = myLength xs + myLength ys := by
  induction xs with
  | nil =>
    simp only [List.nil_append, myLength]
    omega
  | cons x xs ih =>
    simp only [List.cons_append, myLength, ih]
    omega
