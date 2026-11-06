import Mathlib

theorem algebra_306011 : IsLeast {x : ℝ | ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = a * b * c ∧ a * b * c = a ^ 3 ∧ x = a * b + b * c + c * a} 9 := by
  constructor
  · -- Show 9 is in the set
    use Real.sqrt 3, Real.sqrt 3, Real.sqrt 3
    constructor
    · -- Compute a ≠ 0
      positivity
    constructor
    · -- Compute b ≠ 0
      positivity
    constructor
    · -- Compute c ≠ 0
      positivity
    constructor
    · -- Show a + b + c = a * b * c
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - Real.sqrt 3), h1]
    constructor
    · -- Show a * b * c = a ^ 3
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - Real.sqrt 3), h1]
    · -- Show 9 = a * b + b * c + c * a
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - Real.sqrt 3), h1]
  · -- Show 9 is the least
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
    have h_eq4 : b * c = a ^ 2 := by
      have h1' : a ≠ 0 := ha
      have eq1 : a * (b * c) = a ^ 3 := by
        nlinarith
      have h_eq2 : b * c = a ^ 2 := by
        apply (mul_left_inj' h1').mp
        nlinarith
      linarith
    have h_eq6 : b + c = a ^ 3 - a := by
      nlinarith [h1, h2]
    have h_eq7 : x = a ^ 4 := by
      have h_eq8 : x = a * b + b * c + c * a := by
        linarith [h3]
      rw [h_eq8]
      have eq1 : a * b + b * c + c * a = a * (b + c) + b * c := by
        ring
      rw [eq1]
      rw [h_eq4, h_eq6]
      nlinarith
    have h_eq8 : a ^ 2 ≥ 3 := by
      have h_eq9 : (b + c) ^ 2 - 4 * (b * c) ≥ 0 := by
        nlinarith [sq_nonneg (b - c)]
      have h_eq10 : (a ^ 3 - a) ^ 2 - 4 * a ^ 2 ≥ 0 := by
        rw [h_eq6, h_eq4] at h_eq9
        nlinarith
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (a ^ 2 - 3), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_pos_of_ne_zero (show a ≠ 0 by exact ha), sq_nonneg (a^2 + 1), sq_nonneg (a^2 - 3), mul_pos (show 0 < a^2 by positivity) (show 0 < a^2 + 1 by positivity)]
    have h_eq9 : a ^ 4 ≥ 9 := by
      nlinarith [sq_nonneg (a ^ 2 - 3), h_eq8]
    nlinarith [h_eq7, h_eq9]