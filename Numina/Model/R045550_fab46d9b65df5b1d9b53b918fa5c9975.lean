import Mathlib

open Real
open scoped BigOperators

theorem inequalities_319803 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a^2 + b^2 + c^2 - 2*a*b - 2*a*c - 2*b*c < 0) :
  ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y > z ∧ y + z > x ∧ z + x > y ∧
  x = sqrt a ∧ y = sqrt b ∧ z = sqrt c := by 
  use sqrt a, sqrt b, sqrt c 
  constructor
  · -- Show that x > 0, i.e., sqrt a > 0
    positivity 
  constructor 
  · -- Show that y > 0, i.e., sqrt b > 0
    positivity 
  constructor 
  · -- Show that z > 0, i.e., sqrt c > 0 
    positivity 
  constructor 
  · -- Show that x + y > z, i.e., sqrt a + sqrt b > sqrt c
    have h1 : sqrt a > 0 := by positivity 
    have h2 : sqrt b > 0 := by positivity 
    have h3 : sqrt c > 0 := by positivity 
    have h6 : (sqrt a + sqrt b) ^ 2 > c := by 
      have h7 : (sqrt a + sqrt b) ^ 2 = a + b + 2 * (sqrt a * sqrt b) := by 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity)]
      have h8 : (sqrt a * sqrt b) = Real.sqrt (a * b) := by 
        rw [← Real.sqrt_mul (by positivity)]
      have h3' : Real.sqrt (a * b) ^ 2 = a * b := by 
        rw [Real.sq_sqrt]
        positivity 
      have h9 : (sqrt a + sqrt b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by 
        rw [h7]
        have h11 : sqrt a * sqrt b = Real.sqrt (a * b) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h11]
      rw [h9]
      nlinarith [show 0 < a by positivity, show 0 < b by positivity, 
        show 0 < c by positivity, 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sqrt_nonneg (a * b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
          sq_nonneg (a + b - c), 
          sq_nonneg (sqrt a + sqrt b), 
          sq_nonneg (sqrt a - sqrt b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity)
        ]
    have h51 : sqrt a + sqrt b > sqrt c := by 
      have h62 : sqrt ((sqrt a + sqrt b) ^ 2) = sqrt a + sqrt b := by 
        rw [Real.sqrt_sq (show 0 ≤ sqrt a + sqrt b by positivity)]
      have h50 : sqrt a + sqrt b > sqrt c := by 
        have h64 : sqrt c < sqrt a + sqrt b := by
          have h65 : c < (sqrt a + sqrt b) ^ 2 := by 
            linarith [h6]
          have h67 : sqrt c < sqrt ((sqrt a + sqrt b) ^ 2) := by 
            apply Real.sqrt_lt_sqrt 
            all_goals nlinarith 
          rw [h62] at h67 
          linarith 
        linarith 
      linarith 
    linarith 
  constructor 
  · -- Show that y + z > x, i.e., sqrt b + sqrt c > sqrt a
    have h1 : sqrt b > 0 := by positivity 
    have h2 : sqrt c > 0 := by positivity 
    have h3 : sqrt a > 0 := by positivity 
    have h6 : (sqrt b + sqrt c) ^ 2 > a := by 
      have h7 : (sqrt b + sqrt c) ^ 2 = b + c + 2 * (sqrt b * sqrt c) := by 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity)]
      have h8 : (sqrt b * sqrt c) = Real.sqrt (b * c) := by 
        rw [← Real.sqrt_mul (by positivity)]
      have h3' : Real.sqrt (b * c) ^ 2 = b * c := by 
        rw [Real.sq_sqrt]
        positivity 
      have h9 : (sqrt b + sqrt c) ^ 2 = b + c + 2 * Real.sqrt (b * c) := by 
        rw [h7]
        have h11 : sqrt b * sqrt c = Real.sqrt (b * c) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h11]
      rw [h9]
      nlinarith [show 0 < a by positivity, show 0 < b by positivity, 
        show 0 < c by positivity, 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sqrt_nonneg (b * c), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b * c by positivity), 
          sq_nonneg (b + c - a), 
          sq_nonneg (sqrt b + sqrt c), 
          sq_nonneg (sqrt b - sqrt c), 
          Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity)
        ]
    have h51 : sqrt b + sqrt c > sqrt a := by 
      have h62 : sqrt ((sqrt b + sqrt c) ^ 2) = sqrt b + sqrt c := by 
        rw [Real.sqrt_sq (show 0 ≤ sqrt b + sqrt c by positivity)]
      have h50 : sqrt b + sqrt c > sqrt a := by 
        have h64 : sqrt a < sqrt b + sqrt c := by 
          have h65 : a < (sqrt b + sqrt c) ^ 2 := by 
            linarith [h6]
          have h67 : sqrt a < sqrt ((sqrt b + sqrt c) ^ 2) := by 
            apply Real.sqrt_lt_sqrt 
            all_goals nlinarith 
          rw [h62] at h67 
          linarith 
        linarith 
      linarith 
    linarith 
  constructor 
  · -- Show that z + x > y, i.e., sqrt a + sqrt c > sqrt b
    have h1 : sqrt a > 0 := by positivity 
    have h2 : sqrt c > 0 := by positivity 
    have h3 : sqrt b > 0 := by positivity 
    have h6 : (sqrt a + sqrt c) ^ 2 > b := by 
      have h7 : (sqrt a + sqrt c) ^ 2 = a + c + 2 * (sqrt a * sqrt c) := by 
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity)]
      have h8 : (sqrt a * sqrt c) = Real.sqrt (a * c) := by 
        rw [← Real.sqrt_mul (by positivity)]
      have h3' : Real.sqrt (a * c) ^ 2 = a * c := by 
        rw [Real.sq_sqrt]
        positivity 
      have h9 : (sqrt a + sqrt c) ^ 2 = a + c + 2 * Real.sqrt (a * c) := by 
        rw [h7]
        have h11 : sqrt a * sqrt c = Real.sqrt (a * c) := by 
          rw [← Real.sqrt_mul (by positivity)]
        rw [h11]
      rw [h9]
      nlinarith [show 0 < a by positivity, show 0 < b by positivity, 
        show 0 < c by positivity, 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sqrt_nonneg (a * c), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * c by positivity), 
          sq_nonneg (a + c - b), 
          sq_nonneg (sqrt a + sqrt c), 
          sq_nonneg (sqrt a - sqrt c), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity)
        ]
    have h51 : sqrt a + sqrt c > sqrt b := by 
      have h62 : sqrt ((sqrt a + sqrt c) ^ 2) = sqrt a + sqrt c := by 
        rw [Real.sqrt_sq (show 0 ≤ sqrt a + sqrt c by positivity)]
      have h50 : sqrt a + sqrt c > sqrt b := by 
        have h64 : sqrt b < sqrt a + sqrt c := by 
          have h65 : b < (sqrt a + sqrt c) ^ 2 := by 
            linarith [h6]
          have h67 : sqrt b < sqrt ((sqrt a + sqrt c) ^ 2) := by 
            apply Real.sqrt_lt_sqrt 
            all_goals nlinarith 
          rw [h62] at h67 
          linarith 
        linarith 
      linarith 
    linarith 
  constructor 
  · -- Show that x = sqrt a 
    rfl 
  constructor 
  · -- Show that y = sqrt b 
    rfl 
  · -- Show that z = sqrt c 
    rfl