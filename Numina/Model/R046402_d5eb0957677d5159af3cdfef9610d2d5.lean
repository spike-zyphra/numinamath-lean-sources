import Mathlib

theorem algebra_22606 :
    IsGreatest {t : ℝ | ∃ a b c : ℝ, t = |a| + |b| + |c| ∧ (∀ x ∈ Set.Icc 0 1, |a * x ^ 2 + b * x + c| ≤ 1)} 17 := by 
  constructor
  · -- Show that 17 can be achieved
    use 8, -8, 1
    constructor
    · -- Compute |8| + |-8| + |1| and prove it equals 17
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show that |8x^2 - 8x + 1| ≤ 1 for all x ∈ [0, 1]
      intro x hx
      rcases hx with ⟨hx0, hx1⟩
      have h1 : -1 ≤ 8 * x ^ 2 + (-8) * x + 1 ∧ 8 * x ^ 2 + (-8) * x + 1 ≤ 1 := by
        constructor
        · -- Show -1 ≤ 8 * x ^ 2 + (-8) * x + 1
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (x - 1)]
        · -- Show 8 * x ^ 2 + (-8) * x + 1 ≤ 1
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x), sq_nonneg (x - 1)]
      apply abs_le.mpr
      constructor <;> linarith [h1.1, h1.2]
  · -- Show that 17 is the greatest possible value
    intro t ht
    rcases ht with ⟨a, b, c, h1, h⟩
    have h00 : |a * (0: ℝ) ^ 2 + b * (0: ℝ) + c| ≤ 1 := h 0 (by norm_num)
    simp at h00
    have h11 : |a * (1: ℝ) ^ 2 + b * (1: ℝ) + c| ≤ 1 := h 1 (by norm_num)
    norm_num at h11
    have h22 : |a * (1 / 2: ℝ) ^ 2 + b * (1 / 2: ℝ) + c| ≤ 1 := h (1 / 2) (by norm_num)
    norm_num at h22
    cases' abs_cases a with ha1 ha1 <;> cases' abs_cases b with hb1 hb1 <;> cases' abs_cases c with hc1 hc1 <;> 
      linarith [abs_le.mp h00, abs_le.mp h11, abs_le.mp h22]