import Mathlib

/-
The positive integers that satisfy the inequality $2n-5 \lt 5-2n$ are ______ and ______.
-/
theorem algebra_9366 :
    {n : ℤ | n > 0 ∧ 2 * n - 5 < 5 - 2 * n} = {1, 2} := by
  ext n
  simp_all
  constructor <;> intro h
  · -- First, we need to prove that when n > 0 and 2 * n - 5 < 5 - 2 * n, n = 1 or n = 2
    -- Based on the inequality 2n-5 < 5-2n and n being an integer, we can deduce n ≤ 2
    have : n ≤ 2 := by linarith
    -- Since 0 < n, therefore, n = 1 or n = 2.
    match n with
    | Int.ofNat n =>
      match n with
      | 0 => by_contra; exact lt_irrefl 0 h.1
      | 1 => left; rfl
      | 2 => right; rfl
      | n+3 => simp_all; linarith
    | Int.negSucc n => simp_all
  · -- Then we need to prove that when n = 1 or n = 2, 2n-5 < 5-2n, which is obviously true.
    match h with
    | Or.inl h => subst h; simp_all
    | Or.inr h => subst h; simp_all
