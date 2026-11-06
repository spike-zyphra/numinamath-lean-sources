import Mathlib

theorem algebra_18671 : 
    IsLeast {a : ℝ | 0 < a ∧ ∃ x : ℝ, x ^ 6 + 3 * a * x ^ 5 + (3 * a ^ 2 + 3) * x ^ 4 + (a ^ 3 + 6 * a) * x ^ 3 + (3 * a ^ 2 + 3) * x ^ 2 + 3 * a * x + 1 = 0} 2 := by
  constructor
  · -- First part: show that 2 is in the set
    constructor
    · norm_num
    · -- Show that when a = 2, x = -1 is a root
      use -1
      norm_num
  · -- Second part: show that 2 is the least
    intro a ha
    rcases ha with ⟨ha_pos, ⟨x, hx⟩⟩
    have h1 : (x^2 + a * x + 1) ^ 3 = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - x * a + 1), sq_nonneg (x + 1), sq_nonneg (x * (x + a)), sq_nonneg (x * a + 1), sq_nonneg (x^2 + 1), sq_nonneg (x * 1 + 1), sq_nonneg (x + a), sq_nonneg (x * a + x), sq_nonneg (x * (x + 1) * (x + a) * a)]
    have h2 : x^2 + a * x + 1 = 0 := by
      have h3 : (x^2 + a * x + 1) ^ 3 = 0 := h1
      have h4 : (x^2 + a * x + 1) = 0 := by
        have h5 : (x^2 + a * x + 1) ^ 3 = 0 := h3
        simp at h5 ⊢
        <;> nlinarith
      linarith [h4]
    have h3 : a ^ 2 ≥ 4 := by
      nlinarith [sq_nonneg (x + a / 2)]
    have h4 : a ≥ 2 := by
      nlinarith [h3, sq_pos_of_pos ha_pos]
    linarith [h4]