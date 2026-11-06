import Mathlib

theorem algebra_21393 : IsLeast {m | ∃a : ℝ, 0 < a ∧ ∃b : ℝ, 0 < b ∧∃c : ℝ, 0 < c ∧ a^2 = b * c ∧ a + b + c = a * b * c ∧ m = a ^ 2} 3 := by
  constructor
  · -- Show 3 is achievable.
    use Real.sqrt 3
    constructor
    · -- Show 0 < a
      positivity
    use Real.sqrt 3
    constructor
    · -- Show 0 < b
      positivity
    use Real.sqrt 3
    constructor
    · -- Show 0 < c
      positivity
    constructor
    · -- Show a^2 = b * c
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [h1]
    constructor
    · -- Show a + b + c = a * b * c
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h2 : (Real.sqrt 3 : ℝ) ^ 3 = 3 * (Real.sqrt 3 : ℝ) := by
        calc
          (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ) ^ 2 := by ring
          _ = (Real.sqrt 3 : ℝ) * 3 := by rw [h1]
          _ = 3 * (Real.sqrt 3 : ℝ) := by ring
      nlinarith [h1, h2]
    · -- Show m = 3
      have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [h1]
  · -- Show 3 is minimal
    intro m hm
    rcases hm with ⟨a, ha, b, hb, c, hc, h1, h2, hm⟩
    nlinarith [sq_nonneg (a ^ 2 - 3), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]