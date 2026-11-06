import Mathlib

theorem algebra_296745 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + 6 * x + 8)
    (h : ∀ x, f (b * x + c) = 4 * x ^ 2 + 16 * x + 15) :
    c - 2 * b = -3 := by

  have h0 := h 0
  rw [hf] at h0

  have h1 := h 1
  rw [hf] at h1

  have hm1 := h (-1)
  rw [hf] at hm1

  have eq1 : c ^ 2 + 6 * c - 7 = 0 := by 
    nlinarith

  have eq2 : (b + c) ^ 2 + 6 * (b + c) - 27 = 0 := by 
    nlinarith

  have eq3 : (-b + c) ^ 2 + 6 * (-b + c) + 5 = 0 := by 
    nlinarith

  have eq1factored : (c + 7) * (c - 1) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.mp eq1factored) with h_c7 h_c1

  · -- Case 1: c + 7 = 0 → c = -7
    have hc : c = -7 := by linarith

    have eq2_substituted : (b - 10) * (b + 2) = 0 := by 
      rw [hc] at eq2
      nlinarith

    cases' (mul_eq_zero.mp eq2_substituted) with h_b10 h_b2

    · -- Subcase 1a: b - 10 = 0 → b = 10
      have hb : b = 10 := by linarith

      have contradiction : (10 : ℝ) = 0 := by
        rw [hb, hc] at eq3
        nlinarith

      linarith

    · -- Subcase 1b: b + 2 = 0 → b = -2
      have hb : b = -2 := by linarith

      rw [hb, hc]
      norm_num

  · -- Case 2: c - 1 = 0 → c = 1
    have hc : c = 1 := by linarith

    have eq2_substituted : (b - 2) * (b + 10) = 0 := by 
      rw [hc] at eq2
      nlinarith

    cases' (mul_eq_zero.mp eq2_substituted) with h_b2 h_b10

    · -- Subcase 2a: b - 2 = 0 → b = 2
      have hb : b = 2 := by linarith

      rw [hb, hc]
      norm_num

    · -- Subcase 2b: b + 10 = 0 → b = -10
      have hb : b = -10 := by linarith

      have contradiction : (-10 : ℝ) = 0 := by
        rw [hb, hc] at eq3
        nlinarith

      linarith