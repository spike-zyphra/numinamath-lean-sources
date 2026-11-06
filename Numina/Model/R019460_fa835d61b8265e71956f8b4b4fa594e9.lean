import Mathlib

theorem algebra_11447 : IsLeast {x : ℝ | ∃ a b : ℝ, a ≠ 0 ∧ x = a^2 + b^2 ∧
    ∃ t : ℝ, t ∈ Set.Icc 3 4 ∧ a * t^2 + (2 * b + 1) * t - a - 2 = 0} (1 / 100) := by

  constructor
  · -- Show 1/100 is in the set
    use -2 / 25, -3 / 50
    constructor
    · -- Show a ≠ 0
      norm_num
    constructor
    · -- Show x = a^2 + b^2
      norm_num
    · -- Show ∃ t : ℝ, t ∈ Set.Icc 3 4 ∧ a * t^2 + (2 * b + 1) * t - a - 2 = 0
      use 3
      constructor
      · -- Show 3 ∈ [3, 4]
        norm_num [Set.mem_Icc]
      · -- Show a * 3 ^ 2 + (2 * (-3 / 50) + 1) * 3 - (-2 / 25) - 2 = 0
        norm_num

  · -- Show 1/100 is the least
    intro x hx
    rcases hx with ⟨a, b, ha, hx, t, ht, heq⟩

    rw [Set.mem_Icc] at ht
    rcases ht with ⟨ht1, ht2⟩

    nlinarith [sq_nonneg (a + 2 / 25), sq_nonneg (b + 3 / 50), sq_nonneg (t - 3), sq_nonneg (a * (t - 3)), sq_nonneg (b * (t - 3)), sq_nonneg (t * a - b * 2), sq_nonneg ((t -4) * a), sq_nonneg ((t - 4) * b), sq_nonneg (a * b)]