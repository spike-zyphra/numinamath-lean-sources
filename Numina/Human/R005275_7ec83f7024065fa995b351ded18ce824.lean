import Mathlib

inductive Operation where
| add2 | sub3
open Operation

def operate (n : ℤ) (ops : List Operation) : ℤ :=
match ops with
| [] => n
| add2 :: ops => operate (n + 2) ops
| sub3 :: ops => operate (n - 3) ops

-- We show that operate respects List append
lemma operate_comp (x : ℤ) (ops1 ops2 : List Operation) : operate (operate x ops1) ops2 = operate x (ops1 ++ ops2) := by
  revert x
  induction ops1 with
  | nil => simp [operate]
  | cons head tail ih =>
      cases head with
      | add2 =>
          simp [operate]
          intro x
          specialize ih (x+2)
          assumption
      | sub3 =>
          simp [operate]
          intro x
          specialize ih (x-3)
          assumption

-- Utility Mathlib doesn't have
def List.repeat (n : ℕ) (a : A) : List A :=
match n with
| 0 => []
| n+1 => a :: List.repeat n a

-- If we repeatedly add 2 for n times, x become x + 2 * n
lemma operate_add2 (x : ℤ) (n : ℕ) : operate x (List.repeat n add2) = x + 2 * n := by
  revert x
  induction n with
  | zero => simp [operate, List.repeat]
  | succ n ih =>
      simp [operate, List.repeat]
      intro x
      specialize ih (x + 2)
      omega

-- If we repeatedly substract 3 for n times, x become x - 3 * n
lemma operate_sub3 (x : ℤ) (n : ℕ) : operate x (List.repeat n sub3) = x - 3 * n := by
  revert x
  induction n with
  | zero => simp [operate, List.repeat]
  | succ n ih =>
      simp [operate, List.repeat]
      intro x
      specialize ih (x - 3)
      omega

/- Martin and Théo are playing a game: Martin writes an integer on a board.
  Théo then has the right to erase the number and add 2 to it,
  or erase the number and subtract 3 from it, as many times as he wants.
  Théo wins if he manages to get 2020 after a finite number of steps; otherwise, Martin wins.
  Which player has a winning strategy? -/
theorem number_theory_607320 (x : ℤ) : ∃ ops, operate x ops = 2020 := by
  by_cases h : x ≥ 2020
  . -- If x ≥ 2020, assume d = x - 2020.
    -- We first add 2 for d times, then substract 3 for d times.
    -- This includes the case when x = 2020.
    let delta := (x - 2020).toNat
    use List.repeat delta add2 ++ List.repeat delta sub3
    rw [←operate_comp, operate_add2, operate_sub3]
    omega
  . -- If x < 2020, assume d = 2020 - d.
    -- We first add 2 for 2d times, then substract 3 for d times.
    let delta := (2020 - x).toNat
    use List.repeat (2 * delta) add2 ++ List.repeat delta sub3
    rw [←operate_comp, operate_add2, operate_sub3]
    omega
