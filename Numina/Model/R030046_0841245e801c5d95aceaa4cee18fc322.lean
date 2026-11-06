import Mathlib


theorem algebra_9125 :
  IsGreatest {y | ∃ a b c : ℝ,
    0 < a ∧
    0 < b ∧
    0 < c ∧
    a * (a + b + c) = b * c ∧
    y = a / (b + c)}
  ((Real.sqrt 2 - 1) / 2) := by
  constructor
  · -- Show that (Real.sqrt 2 - 1) / 2 is in the set.
    use Real.sqrt 2 - 1, 1, 1
    constructor
    · -- Show that 0 < Real.sqrt 2 - 1.
      have h1 : Real.sqrt 2 > 1 := by
        have h1 : Real.sqrt 2 > Real.sqrt 1 := by apply Real.sqrt_lt_sqrt; all_goals norm_num
        have h2 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
        linarith [h1, h2]
      linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), h1]
    constructor
    · -- Show that 0 < (1 : ℝ)
      norm_num
    constructor
    · -- Show that 0 < (1 : ℝ)
      norm_num
    constructor
    · -- Show that (Real.sqrt 2 - 1) * ((Real.sqrt 2 - 1) + 1 + 1) = 1 * 1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show that (Real.sqrt 2 - 1) / (1 + 1) = (Real.sqrt 2 - 1) / 2
      ring_nf
  · -- Show that (Real.sqrt 2 - 1) / 2 is the greatest element in the set
    intro y hy
    rcases hy with ⟨a, b, c, ha, hb, hc, h1, hy⟩
    have h2 : 0 < b + c := by linarith
    have h3 : (b - c) ^ 2 ≥ 0 := by nlinarith
    have h4 : b * c ≤ ((b + c) / 2) ^ 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h5 : a ^ 2 + a * (b + c) ≤ ((b + c) / 2) ^ 2 := by
      nlinarith [h1, h4]
    have h6 : (a / (b + c)) ^ 2 + (a / (b + c)) ≤ 1 / 4 := by
      have h7 : 0 < (b + c) ^ 2 := by positivity
      have h8 : a ^ 2 + a * (b + c) ≤ ((b + c) / 2) ^ 2 := h5
      have h9 : (a ^ 2 + a * (b + c)) / ((b + c) ^ 2) ≤ ((b + c) / 2) ^ 2 / ((b + c) ^ 2) := by
        apply (div_le_div_right (by positivity)).mpr
        linarith
      have h10 : (a ^ 2 + a * (b + c)) / ((b + c) ^ 2) = (a / (b + c)) ^ 2 + (a / (b + c)) := by
        field_simp
        ring
      have h11 : ((b + c) / 2) ^ 2 / ((b + c) ^ 2) = 1 / 4 := by
        field_simp
        nlinarith
      rw [h10] at h9
      rw [h11] at h9
      linarith
    have h10 : a / (b + c) ≤ (Real.sqrt 2 - 1) / 2 := by
      have h11 : (a / (b + c)) ^ 2 + (a / (b + c)) - 1 / 4 ≤ 0 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((a / (b + c)) - (Real.sqrt 2 - 1) / 2), sq_nonneg ((a / (b + c)) + (Real.sqrt 2 + 1) / 2)]
    have h11 : y = a / (b + c) := by linarith [hy]
    linarith [h11, h10]