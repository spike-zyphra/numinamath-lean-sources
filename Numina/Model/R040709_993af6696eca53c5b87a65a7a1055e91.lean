import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

open Real
open scoped EuclideanGeometry

theorem inequalities_123265
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c^2 = a^2 + b^2) :
  a + b ≤ c * sqrt 2 ∧
  (a + b = c * sqrt 2 ↔ a = b) := by

  have h2 : 0 < a := h₀.1
  have h3 : 0 < b := h₀.2.1
  have h4 : 0 < c := h₀.2.2

  -- We will first prove the inequality a + b ≤ c * sqrt 2.
  have h5 : (a + b) ^ 2 ≤ 2 * c ^ 2 := by
    have h6 : c ^ 2 = a ^ 2 + b ^ 2 := h₁
    nlinarith [sq_nonneg (a - b)]

  have h6 : a + b ≤ c * Real.sqrt 2 := by
    have h7 : (a + b) ^ 2 ≤ 2 * c ^ 2 := h5
    have h7' : (a + b) ^ 2 ≤ 2 * c ^ 2 := h5
    have h8 : Real.sqrt ((a + b) ^ 2) ≤ Real.sqrt (2 * c ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h9 : Real.sqrt ((a + b) ^ 2) = a + b := by
      rw [Real.sqrt_sq (by positivity)]
    have h10 : Real.sqrt (2 * c ^ 2) = c * Real.sqrt 2 := by
      have h11 : Real.sqrt (2 * c ^ 2) = Real.sqrt 2 * Real.sqrt (c ^ 2) := by 
        rw [Real.sqrt_mul (by nlinarith)]
      have h12 : Real.sqrt (c ^ 2) = c := by
        rw [Real.sqrt_sq (by linarith)]
      rw [h12] at h11
      rw [h11]
      ring 
    rw [h9] at h8 
    rw [h10] at h8
    linarith
  -- Now we will prove the equality condition.

  constructor 
  · -- Show the inequality
    exact h6
  · -- Show the equality condition
    constructor
    · -- Assume a + b = c * sqrt 2, derive a = b
      intro heq
      have h7 : (a + b) ^ 2 = 2 * c ^ 2 := by 
        calc
          (a + b) ^ 2 = (c * Real.sqrt 2) ^ 2 := by 
            rw [show c * Real.sqrt 2 = a + b by linarith [heq]]
          _ = c^2 * (Real.sqrt 2) ^2 := by ring 
          _ = c ^ 2 * (2 : ℝ) := by 
            rw [Real.sq_sqrt] 
            all_goals linarith 
          _ = 2 * c ^ 2 := by 
            ring
      have h8 : (a - b) ^ 2 = 0 := by 
        have h9 : c^2 = a^2 + b^2 := h₁
        nlinarith 
      have h10 : a - b = 0 := by 
        nlinarith 
      linarith 
    · -- Assume a = b, prove a + b = c * sqrt 2
      intro heq
      have h11 : a = b := by linarith 
      have h12 : c ^ 2 = 2 * a ^ 2 := by 
        have h13 : b = a := by linarith [h11] 
        rw [h13] at h₁ 
        nlinarith 
      have h13 : c = a * Real.sqrt 2 := by
        have h14 : c ≥ 0 := by linarith [show 0 < c from by linarith] 
        have h15 : c ^ 2 = 2 * a ^ 2 := h12 
        have h16 : c = Real.sqrt (2 * a ^ 2) := by
          rw [← h15]
          field_simp [h14]
        rw [h16]
        have h17 : Real.sqrt (2 * a ^ 2) = Real.sqrt 2 * Real.sqrt (a ^ 2) := by 
          rw [Real.sqrt_mul (by nlinarith)]
        rw [h17]
        have h18 : Real.sqrt (a ^ 2) = a := by 
          rw [Real.sqrt_sq (by linarith [show 0 < a from by linarith])]
        rw [h18]
        all_goals ring 
      calc
        a + b = a + a := by 
          rw [show b = a by linarith] 
        _ = 2 * a := by ring 
        _ = (a * Real.sqrt 2) * Real.sqrt 2 := by
          have h7 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [Real.sqrt_nonneg 2] 
        _ = (c) * Real.sqrt 2 := by 
          rw [h13] 
        _ = c * Real.sqrt 2 := by ring