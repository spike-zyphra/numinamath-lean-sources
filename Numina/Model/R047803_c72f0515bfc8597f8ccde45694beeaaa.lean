import Mathlib

theorem inequalities_148508 (a : ℝ) :
    (∀ x : ℝ, (a - 2) * x ^ 2 + 2 * (a - 2) * x - 4 < 0) ↔ a ∈ Set.Ioc (-2) 2 := by
  constructor
  · -- Assume the inequality holds for all x, prove a ∈ (-2, 2]
    intro h
    constructor
    · -- Show a > -2
      by_contra h4
      push_neg at h4
      have h3 : a ≤ -2 := by linarith
      have h4 : (a - 2) * (-1 : ℝ) ^ 2 + 2 * (a - 2) * (-1 : ℝ) - 4 ≥ 0 := by
        nlinarith
      have h5 : (a - 2) * (-1 : ℝ) ^ 2 + 2 * (a - 2) * (-1 : ℝ) - 4 < 0 := h (-1 : ℝ)
      linarith
    · -- Show a ≤ 2
      by_contra h2
      push_neg at h2
      have h3 : a - 2 > 0 := by linarith
      have h4 : (a - 2) * (2 / (a - 2)) ^ 2 + 2 * (a - 2) * (2 / (a - 2)) - 4 ≥ 0 := by
        have h4 : (a - 2) * (2 / (a - 2)) ^ 2 + 2 * (a - 2) * (2 / (a - 2)) - 4 = 4 / (a - 2) := by
          field_simp [show a - 2 ≠ 0 by linarith]
          <;> nlinarith
        rw [h4]
        have h3 : (a - 2 : ℝ) > 0 := by linarith
        have h6 : 4 / (a - 2) > 0 := by apply div_pos; norm_num; all_goals linarith
        linarith
      have h8 : (a - 2) * (2 / (a - 2)) ^ 2 + 2 * (a - 2) * (2 / (a - 2)) - 4 < 0 := h (2 / (a - 2))
      linarith
  · -- Assume a ∈ (-2, 2], prove the inequality holds for all x
    rintro ⟨ha1, ha2⟩
    intro x
    have h1 : (a - 2) * x ^ 2 + 2 * (a - 2) * x - 4 < 0 := by
      have h1 : (a - 2) * x ^ 2 + 2 * (a - 2) * x - 4 = (a - 2) * (x + 1) ^ 2 - (a - 2) - 4 := by
        nlinarith
      rw [h1]
      nlinarith [sq_nonneg (x + 1), sq_nonneg (a - 2), sq_nonneg ((x + 1) * (a - 2)), mul_nonneg (show 0 ≤ (2 + a) by linarith) (show 0 ≤ (2 - a) by nlinarith)]
    linarith