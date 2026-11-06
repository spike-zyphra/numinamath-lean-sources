import Mathlib

theorem algebra_167689 (a : ℝ) :
    (∃ x : ℝ, 3 * 4 ^ (x - 2) + 27 = a + a * 4 ^ (x - 2)) ↔ 3 < a ∧ a < 27 := by
  constructor
  · -- Assume that there exists an x satisfying the equation, prove 3 < a ∧ a < 27
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : (4 : ℝ) ^ (x - 2) > 0 := by positivity
    have h2 : 3 * (4 : ℝ) ^ (x - 2) + 27 = a + a * (4 : ℝ) ^ (x - 2) := by linarith
    have h3 : (3 - a) * (4 : ℝ) ^ (x - 2) = a - 27 := by
      linarith
    have h4 : (4 : ℝ) ^ (x - 2) > 0 := h1
    have h7 : (3 - a) * (4 : ℝ) ^ (x - 2) = a - 27 := h3
    have h8 : (3 - a) * (4 : ℝ) ^ (x - 2) = a - 27 := h3
    have h9 : a - 27 > 0 ∨ a - 27 < 0 := by
      by_contra h
      push_neg at h
      have h10 : a - 27 = 0 := by linarith
      rw [h10] at h8
      have : (3 - a) * (4 : ℝ) ^ (x - 2) = 0 := by linarith
      have h11 : (4 : ℝ) ^ (x - 2) > 0 := h1
      have h12 : 3 - a = 0 := by
        nlinarith
      have h13 : a = 3 := by linarith
      have h14 : a - 27 = 0 := by linarith
      linarith
    rcases h9 with h9 | h9
    · -- Case where a > 27
      have h10 : (3 - a) * (4 : ℝ) ^ (x - 2) > 0 := by nlinarith
      have h11 : 3 - a > 0 := by nlinarith
      have h12 : a < 3 := by linarith
      linarith
    · -- Case where a < 27
      have h14 : (3 - a) * (4 : ℝ) ^ (x - 2) < 0 := by nlinarith
      have h11 : 3 - a < 0 := by nlinarith
      have h12 : a > 3 := by linarith
      have h13 : a < 27 := by
        nlinarith
      constructor
      · linarith
      · linarith
  · -- Assume 3 < a ∧ a < 27, prove ∃ x : ℝ, 3 * 4 ^ (x - 2) + 27 = a + a * 4 ^ (x - 2)
    rintro ⟨ha1, ha2⟩
    use 2 + Real.logb (4) ((a - 27) / (3 - a))
    have h1 : (a - 27 : ℝ) / (3 - a) > 0 := by
      apply div_pos_of_neg_of_neg
      · -- a - 27 < 0
        nlinarith
      · -- 3 - a < 0
        nlinarith
    have h2 : (4 : ℝ) ^ (2 + Real.logb (4) ((a - 27) / (3 - a)) - 2) = (a - 27) / (3 - a) := by
      have h15 : (2 + Real.logb (4) ((a - 27) / (3 - a)) - 2 : ℝ) = Real.logb (4) ((a - 27) / (3 - a)) := by
        ring
      rw [h15]
      rw [Real.rpow_logb]
      all_goals
        nlinarith
    rw [h2]
    field_simp [(show (3 - (a : ℝ) ) ≠ 0 by linarith)] at *
    <;> nlinarith