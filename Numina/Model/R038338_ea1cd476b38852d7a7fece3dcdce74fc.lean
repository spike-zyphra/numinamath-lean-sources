import Mathlib

theorem algebra_110213 {a : ℕ → ℝ} (h : ∀ n, (3 - a (n + 1)) * (6 + a n) = 18) (ha : a 0 = 3) :
    ∑ i in Finset.range (n + 1), (1 / a i) = (2 ^ (n + 2) - n - 3) / 3 := by

  have ha1 : ∀ n, a n > 0 := by
    intro n
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      have eq1 := h n
      nlinarith [sq_nonneg (a n - 3), sq_nonneg (a (n + 1) - 1), ih]

  -- Show the relation for 1/a_{n+1}
  have h1 : ∀ (n : ℕ), 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := by
    intro n
    have eq1 := h n
    have h2 : a n > 0 := ha1 n
    have h3 : a (n + 1) > 0 := ha1 (n + 1)
    field_simp [show a n ≠ 0 by linarith, show a (n + 1) ≠ 0 by linarith] at eq1 ⊢
    nlinarith [sq_nonneg (a n), sq_nonneg (a (n + 1)), mul_pos h2 h3]

  -- Prove the formula for 1/a_n
  have h2 : ∀ (n : ℕ), (1 / a n) = (2 ^ (n + 1) - 1) / 3 := by
    intro n
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      have h3 : 1 / a (n + 1) = 2 * (1 / a n) + 1 / 3 := h1 n
      rw [h3, ih]
      field_simp at *
      ring

  -- Prove the final sum formula using induction
  have h3 : ∀ (n : ℕ), ∑ i in Finset.range (n + 1), (1 / a i) = (2 ^ (n + 2) - n - 3) / 3 := by
    intro n
    induction n with
    | zero =>
      norm_num [ha, h2]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [h2 (n + 1)]
      field_simp at *
      ring
  exact h3 n