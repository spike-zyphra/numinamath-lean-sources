import Mathlib

theorem algebra_101564 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 8) (h₁ : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    ⌊e⌋ ≤ 3 := by
  have h2 : a + b + c + d = 8 - e := by
    linarith
  have h3 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 16 - e ^ 2 := by
    nlinarith
  have h4 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ (1 / 4) * (a + b + c + d) ^ 2 := by
    linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h2, h3] at h4
  have h5 : e ≤ (16 / 5 : ℝ) := by
    nlinarith
  have h6 : e < (4 : ℝ) := by
    nlinarith
  have h7 : ⌊e⌋ ≤ 3 := by
    by_contra h
    push_neg at h
    have h8 : ⌊e⌋ ≥ 4 := by
      omega
    have h9 : (4 : ℝ) ≤ e := by
      have h10 : (4 : ℝ) ≤ e := by
        have h11 : ⌊e⌋ ≥ 4 := h8
        have h12 : (⌊e⌋ : ℝ) ≥ (4 : ℝ) := by
          exact_mod_cast h11
        have h13 : (⌊e⌋ : ℝ) ≤ e := Int.floor_le e
        nlinarith [h12, h13]
      linarith
    linarith
  exact h7