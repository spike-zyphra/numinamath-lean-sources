import Mathlib

/-In the sequence 2001, 2002, 2003, ... , each term after the third is found by
subtracting the previous term from the sum of the two terms that precede that term.
For example, the fourth term is 2001 + 2002 - 2003 = 2000. What is the 2004th term
in this sequence?
(A) - 2004 () - 2 (C) 0 (D) 4003 (E) 6007-/


def f : ℕ → ℤ
| 0 => 2001
| 1 => 2002
| 2 => 2003
| n + 3 => f n + f (n + 1) - f (n + 2)

theorem algebra_95405 : f 2003 = 0 := by
-- we use the following three cases to incorporate the recurrence relation.
  have f_formula : ∀ k : ℕ, f (2 * k + 2) = 2003 + 2 * k
    ∧ f (2 * k + 1) = 2002 - 2 * k
    ∧ f (2 * k) = 2001 + 2 * k := by
    intro k
    induction k with
    | zero =>
      -- Base case: k = 0
      simp
      constructor
      · rfl  -- f(0) = 2003 + 2(0)
      constructor
      · rfl  -- f(1) = 2002 - 2(0)
      · rfl  -- f(2) = 2003 + 2(0)

    | succ k ih =>
      -- Inductive step: Assume the formulas hold for k, prove for k+1
      constructor
      · calc
          f (2 * (k + 1) + 2) = f (2 * k + 4) := by ring_nf
          _ = f (2 * k + 1) + f (2 * k +2) - f (2 * k + 3) := by rfl
          _ = f (2 * k + 1) + f (2 * k + 2) - (f (2 * k) + f (2 * k +1) - f (2 * k +2)) := by rfl
          _ = f (2 * k + 2) + f (2 * k + 2) - f (2 * k) := by ring_nf
          _ = (2003 + 2 * k)+ (2003 + 2 * k) - (2001 + 2 * k) := by rw [ih.1, ih.2.2]
          _ = 2005 + 2 * k := by ring_nf
          _ = 2003 + 2 * (k +1) := by ring_nf
      constructor
      · calc
          f (2 * (k + 1) + 1) = f (2 * k + 3) := by ring_nf
          _ = f (2 * k) + f (2 * k + 1) - f (2 * k + 2) := by rfl
          _ = (2001 + 2 * k) + (2002 - 2 * k) - (2003 + 2 * k) := by rw [ih.2.2, ih.2.1, ih.1]
          _ = 2000 - 2 * k := by ring
          _ = 2002 - 2 * (k + 1) := by ring
      · calc
          f (2 * (k + 1)) = f (2 * k + 2) := by ring_nf
          _ = 2003 + 2 * k := by rw [ih.1]
          _ = 2001 + 2 * (k + 1) := by ring_nf

  -- Applying this formula for k = 1001
  have result := f_formula 1001
  exact result.2.1  -- Extract f(2003) = 0