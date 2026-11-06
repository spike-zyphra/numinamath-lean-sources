import Mathlib

theorem algebra_14822 : {b : ℝ | ∃ x : ℝ, x ^ 2 + b * x + 16 = 0} = Set.Iic (-8) ∪ Set.Ici 8 := by
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
  constructor
  · -- Assume there ∃ x : ℝ, x ^ 2 + b * x + 16 = 0, show b ≤ -8 or b ≥ 8
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : (x + b / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h2 : b ^ 2 ≥ 64 := by
      nlinarith
    by_cases h3 : b ≥ 0
    · -- If b ≥ 0, then b ≥ 8
      have h5 : b ≥ 8 := by
        nlinarith [h2, h3]
      right
      linarith
    · -- If b < 0, then b ≤ -8
      have h6 : b ≤ -8 := by
        nlinarith [h2, show b ≤ 0 by linarith]
      left
      linarith
  · -- Assume b ≤ -8 or b ≥ 8, show ∃ x : ℝ, x ^ 2 + b * x + 16 = 0
    rintro (hb | hb)
    · -- Case where b ≤ -8
      have hb2 : b ^ 2 ≥ 64 := by nlinarith
      use (-b + Real.sqrt (b ^ 2 - 64)) / 2
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 64), Real.sq_sqrt (show (b ^ 2 - 64 : ℝ) ≥ 0 by nlinarith)]
    · -- Case where b ≥ 8
      have hb2 : b ^ 2 ≥ 64 := by nlinarith
      use (-b + Real.sqrt (b ^ 2 - 64)) / 2
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 64), Real.sq_sqrt (show (b ^ 2 - 64 : ℝ) ≥ 0 by nlinarith)]