import Mathlib

theorem algebra_606369 (a : ℕ → ℝ) (h0 : a 0 > 0) (hn : ∀ n : ℕ, a (n + 1) = a n / √(1 + 2020 * (a n) ^ 2)) : a 2020 < 1 / 2020 := by

  have h1 : ∀ n : ℕ, a n ^ 2 = a 0 ^ 2 / (1 + (n : ℝ) * 2020 * a 0 ^ 2) := by
    intro n
    induction n with
    | zero =>
      field_simp
    | succ n ih =>
      have h2 : a (n + 1) = a n / √(1 + 2020 * (a n) ^ 2) := by
        specialize hn n
        simpa using hn
      have h4 : a (n + 1) ^ 2 = (a n) ^ 2 / (1 + 2020 * (a n) ^ 2) := by
        rw [h2]
        have h5 : (√(1 + 2020 * (a n) ^ 2)) ^ 2 = 1 + 2020 * (a n) ^ 2 := by
          exact Real.sq_sqrt (by positivity)
        field_simp [h5]
        <;> nlinarith [Real.sqrt_nonneg (1 + 2020 * (a n) ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + 2020 * (a n) ^ 2) by positivity)]
      rw [h4]
      rw [ih]
      field_simp
      ring_nf

  have h2 : a 2020 ^ 2 < (1 / 2020) ^ 2 := by
    have h3 : a 2020 ^ 2 = a 0 ^ 2 / (1 + (2020 : ℝ) * 2020 * a 0 ^ 2) := by
      specialize h1 2020
      norm_num at h1 ⊢
      linarith
    rw [h3]
    have h4 : a 0 > 0 := h0
    have h5 : a 0 ^ 2 > 0 := by
      nlinarith [h4]
    have h6 : 0 < (1 + (2020 : ℝ) * 2020 * a 0 ^ 2) := by
      nlinarith [h4]
    have h7 : (a 0 ^ 2 / (1 + (2020 : ℝ) * 2020 * a 0 ^ 2)) < (1 / 2020) ^ 2 := by
      have h8 : (1 / 2020 : ℝ) ^ 2 = 1 / (2020 ^ 2 : ℝ) := by
        norm_num
      rw [h8]
      have h9 : a 0 ^ 2 / (1 + (2020 : ℝ) * 2020 * a 0 ^ 2) < 1 / (2020 ^ 2 : ℝ) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_pos_of_pos h4]
      linarith
    linarith

  have h3 : a 2020 > 0 := by
    have h4 : ∀ n : ℕ, a n > 0 := by
      intro n
      induction n with
      | zero =>
        exact h0
      | succ n ih =>
        have h2 : a (n + 1) = a n / √(1 + 2020 * (a n) ^ 2) := by
          specialize hn n
          simpa using hn
        rw [h2]
        apply div_pos
        exact ih
        positivity
    specialize h4 2020
    linarith

  nlinarith [sq_nonneg (a 2020 - 1 / 2020), h3]