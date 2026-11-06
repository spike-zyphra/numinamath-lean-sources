import Mathlib

open Real
open scoped BigOperators

theorem inequalities_137864 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y > z ∧ y + z > x ∧ z + x > y ∧
  x = sqrt a ∧ y = sqrt b ∧ z = sqrt c ∧
  sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ≤ a + b + c ∧
  a + b + c ≤ 2 * sqrt (a * b) + 2 * sqrt (b * c) + 2 * sqrt (c * a) := by

  use Real.sqrt a, Real.sqrt b, Real.sqrt c
  constructor
  · -- Show that 0 < x
    positivity
  constructor
  · -- Show that 0 < y
    positivity
  constructor
  · -- Show that 0 < z
    positivity
  constructor
  · -- Show that x + y > z
    have h1 : Real.sqrt a + Real.sqrt b > Real.sqrt c := by
      have h2 : (Real.sqrt a + Real.sqrt b) ^ 2 > (Real.sqrt c : ℝ) ^ 2 := by
        have h3 : (Real.sqrt a + Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) := by ring
        rw [h3]
        have ha2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
        have hb2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
        have hc2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
        rw [ha2, hb2, hc2]
        nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (c * a),
          Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ b * c by positivity), Real.sq_sqrt (show 0 ≤ c * a by positivity),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      have h4 : Real.sqrt a + Real.sqrt b ≥ 0 := by
        positivity
      have h5 : Real.sqrt c ≥ 0 := by
        positivity
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
    linarith
  constructor
  · -- Show that y + z > x
    have h1 : Real.sqrt b + Real.sqrt c > Real.sqrt a := by
      have h2 : (Real.sqrt b + Real.sqrt c) ^ 2 > (Real.sqrt a : ℝ) ^ 2 := by
        have h3 : (Real.sqrt b + Real.sqrt c) ^ 2 = (Real.sqrt b) ^ 2 + (Real.sqrt c) ^ 2 + 2 * (Real.sqrt b * Real.sqrt c) := by ring
        rw [h3]
        have ha2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
        have hb2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
        have hc2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
        rw [ha2, hb2, hc2]
        nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (c * a),
          Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ b * c by positivity), Real.sq_sqrt (show 0 ≤ c * a by positivity),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      have h4 : Real.sqrt b + Real.sqrt c ≥ 0 := by
        positivity
      have h5 : Real.sqrt a ≥ 0 := by
        positivity
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
    linarith
  constructor
  · -- Show that z + x > y
    have h1 : Real.sqrt c + Real.sqrt a > Real.sqrt b := by
      have h2 : (Real.sqrt c + Real.sqrt a) ^ 2 > (Real.sqrt b : ℝ) ^ 2 := by
        have h3 : (Real.sqrt c + Real.sqrt a) ^ 2 = (Real.sqrt c) ^ 2 + (Real.sqrt a) ^ 2 + 2 * (Real.sqrt c * Real.sqrt a) := by ring
        rw [h3]
        have ha2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
        have hb2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
        have hc2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt (by linarith)
        rw [ha2, hb2, hc2]
        nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (c * a),
          Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ b * c by positivity), Real.sq_sqrt (show 0 ≤ c * a by positivity),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      have h4 : Real.sqrt c + Real.sqrt a ≥ 0 := by
        positivity
      have h5 : Real.sqrt b ≥ 0 := by
        positivity
      nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
    linarith
  constructor
  · -- Show that x = sqrt a
    rfl
  constructor
  · -- Show that y = sqrt b
    rfl
  constructor
  · -- Show that z = sqrt c
    rfl
  constructor
  · -- Show that sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ≤ a + b + c
    have h1 : Real.sqrt (a * b) ≤ (a + b) / 2 := by
      have h5 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
        rw [Real.sqrt_mul (by linarith)]
      rw [h5] at *
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
    have h1'' : Real.sqrt (b * c) ≤ (b + c) / 2 := by
      have h5 : Real.sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
        rw [Real.sqrt_mul (by linarith)]
      rw [h5] at *
      nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt c), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sqrt_nonneg b, Real.sqrt_nonneg c, mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]
    have h1''' : Real.sqrt (c * a) ≤ (c + a) / 2 := by
      have h5 : Real.sqrt (c * a) = Real.sqrt c * Real.sqrt a := by
        rw [Real.sqrt_mul (by linarith)]
      rw [h5] at *
      nlinarith [sq_nonneg (Real.sqrt c - Real.sqrt a), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sqrt_nonneg c, Real.sqrt_nonneg a, mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a)]
    linarith
  · -- Show that a + b + c ≤ 2 * sqrt (a * b) + 2 * sqrt (b * c) + 2 * sqrt (c * a)
    have h1 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (by linarith)]
    have h2 : Real.sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
      rw [Real.sqrt_mul (by linarith)]
    have h3 : Real.sqrt (c * a) = Real.sqrt c * Real.sqrt a := by
      rw [Real.sqrt_mul (by linarith)]
    rw [h1, h2, h3] at *
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt b - Real.sqrt c), sq_nonneg (Real.sqrt c - Real.sqrt a),
      Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (b * c), Real.sqrt_nonneg (c * a),
      Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ b * c by positivity), Real.sq_sqrt (show 0 ≤ c * a by positivity),
      Real.sq_sqrt (show 0 ≤ a by linarith), Real.sq_sqrt (show 0 ≤ b by linarith), Real.sq_sqrt (show 0 ≤ c by linarith),
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c), mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]