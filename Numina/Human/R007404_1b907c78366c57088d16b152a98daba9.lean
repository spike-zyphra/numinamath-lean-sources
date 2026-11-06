import Mathlib


/-
The solution set of the inequality $x^2 + x - 2 < 0$ is \_\_\_\_\__.
-/
theorem algebra_9021 (x : ℝ) :
    x ^ 2 + x - 2 < 0 ↔ -2 < x ∧ x < 1 := by

  --  we first need to factor the quadratic expression on the left-hand side. We can factor it as: $(x + 2)(x - 1) < 0$
  rw [show x ^ 2 + x - 2 = (x + 2) * (x - 1) by ring]

  -- For $x < -2$, both factors $(x + 2)$ and $(x - 1)$ are negative, which makes the product positive.
  rcases lt_or_le x (-2) with h1 | h1
  . have : ¬ (x + 2) * (x - 1) < 0 := by
      apply not_lt.mpr
      apply mul_nonneg_of_nonpos_of_nonpos
      <;> linarith
    simp only [this, false_iff]
    apply not_and_or.mpr
    left
    linarith

  -- For $x = -2$, we can easily verify it.
  rcases eq_or_ne x (-2) with h2 | h2
  . simp_all

  -- For $-2 < x < 1$, the factor $(x + 2)$ is positive while $(x - 1)$ is negative, thus the product is negative.
  apply (fun x => lt_of_le_of_ne x h2.symm) at h1
  rcases lt_or_le x 1 with h3 | h3
  . have : (x + 2) * (x - 1) < 0 := by
      apply mul_neg_of_pos_of_neg
      <;> linarith
    simp only [this, true_iff, h3, h1, and_true]

  -- For $x = 1$, we can easily verify it.
  rcases eq_or_ne x 1 with h4 | h4
  . simp_all

  -- For $x > 1$, both factors $(x + 2)$ and $(x - 1)$ are positive, which makes the product positive again.
  --apply (fun x => lt_of_le_of_ne x h4.symm) at h3
  apply (fun x => lt_of_le_of_ne x h4.symm) at h3
  have : ¬ (x + 2) * (x - 1) < 0 := by
    apply not_lt.mpr
    apply Left.mul_nonneg
    <;> linarith
  simp only [this, false_iff]
  apply not_and_or.mpr
  right
  linarith
