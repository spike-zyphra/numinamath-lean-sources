import Mathlib

open Finset Real

theorem algebra_220036 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n > 1, a n = a (n - 1) / (2 * n * a (n - 1) + 1)) (k : ℕ) :
    ∑ i ∈ Icc 1 k, a i = k / (k + 1) := by

  -- first, we need to prove that $a_n = \frac{1}{n(n+1)}$ using induction
  have h1 : ∀ n, a (n + 1) = 1 / ((n + 1) * ((n + 1) + 1 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      -- Base case: a_1 = 1/2
      rw [ha1]
      norm_num
    | succ n ih =>
      -- Induction hypothesis: a (n + 1) = 1 / ((n + 1) * ((n + 1) + 1))
      -- We need to prove for a (n + 2)
      have ha2 : a (n + 2) = a (n + 1) / (2 * (n + 2) * a (n + 1) + 1) := by
        specialize han (n + 2) (by linarith)
        simpa using han
      rw [ha2]
      rw [ih]
      field_simp
      ring
  -- Then we need to apply the formula to compute the sum
  have h2 : ∀ (k : ℕ), ∑ i ∈ Icc 1 k, a i = k / (k + 1) := by
    intro k
    induction k with
    | zero =>
      -- Base case: sum from 1 to 0 is empty
      simp
    | succ k ih =>
      -- use the induction hypothesis
      rw [sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h3 : a (k + 1) = 1 / ((k + 1) * ((k + 1) + 1 : ℝ)) := h1 k
      simp [h3]
      field_simp
      ring
  exact h2 k