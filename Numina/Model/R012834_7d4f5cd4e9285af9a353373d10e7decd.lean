import Mathlib

open Real Set
open scoped Real

theorem inequalities_272288 (a b c x : ℝ) :
  -sin ((π/4) - (b-c)/2)^2 ≤ sin (a*x+b) * cos (a*x+c) ∧
  sin (a*x+b) * cos (a*x+c) ≤ cos ((π/4) - (b-c)/2)^2 := by

  have h1 : sin (a * x + b) * cos (a * x + c) = (1 / 2) * (sin (2 * a * x + b + c) + sin (b - c)) := by
    have h2 : sin (a * x + b) * cos (a * x + c) = (1 / 2) * (sin ((a * x + b + (a * x + c))) + sin ((a * x + b - (a * x + c)))) := by
      rw [show sin ((a * x + b + (a * x + c))) = sin ((a * x + b) + (a * x + c)) by ring_nf, 
      show sin ((a * x + b - (a * x + c))) = sin ((a * x + b) - (a * x + c)) by ring_nf]
      have h6 : sin ( (a * x + b) + (a * x + c) ) = sin (a * x + b) * cos (a * x + c) + cos (a * x + b) * sin (a * x + c) := by rw [sin_add]
      have h7 : sin ( (a * x + b) - (a * x + c) ) = sin (a * x + b) * cos (a * x + c) - cos (a * x + b) * sin (a * x + c) := by rw [sin_sub]
      linarith [h6, h7]
    have h3 : sin ((a * x + b + (a * x + c))) = sin (2 * a * x + b + c) := by ring_nf
    have h4 : sin ((a * x + b - (a * x + c))) = sin (b - c) := by ring_nf
    rw [h3, h4] at h2
    linarith

  have h2 : cos ((π / 4) - (b - c) / 2) ^ 2 = (1 + sin (b - c)) / 2 := by
    have h7 : cos ((π / 4) - (b - c) / 2) ^ 2 = (1 + cos (2 * ((π / 4) - (b - c) / 2)) ) / 2 := by 
      rw [cos_sq]
      <;> ring_nf
    have h8 : cos (2 * ((π / 4) - (b - c) / 2)) = sin (b - c) := by 
      have h9 : 2 * ((π / 4) - (b - c) / 2) = (π / 2) - (b - c) := by 
        ring_nf
      have h10 : cos (2 * ((π / 4) - (b - c) / 2)) = cos ((π / 2) - (b - c)) := by 
        rw [h9]
      have h11 : cos ((π / 2) - (b - c)) = sin (b - c) := by 
        rw [cos_pi_div_two_sub]
      rw [h10, h11]
    rw [h7, h8]
    <;> ring_nf <;> field_simp [pi_ne_zero] <;> ring_nf
  
  have h9 : sin ((π / 4) - (b - c) / 2) ^ 2 = (1 - sin (b - c)) / 2 := by 
    have h8 : sin ((π / 4) - (b - c) / 2) ^ 2 = (1 - cos (2 * ((π / 4) - (b - c) / 2)) ) / 2 := by 
      rw [sin_sq_eq_half_sub]
      <;> ring_nf
    have h10 : cos (2 * ((π / 4) - (b - c) / 2)) = sin (b - c) := by 
      have h11 : 2 * ((π / 4) - (b - c) / 2) = (π / 2) - (b - c) := by 
        ring_nf
      have h12 : cos (2 * ((π / 4) - (b - c) / 2)) = cos ((π / 2) - (b - c)) := by 
        rw [h11]
      have h13 : cos ((π / 2) - (b - c)) = sin (b - c) := by 
        rw [cos_pi_div_two_sub]
      rw [h12, h13]
    rw [h8, h10]
    <;> ring_nf <;> field_simp [pi_ne_zero] <;> ring_nf
  
  constructor
  · -- Proof of the lower bound
    rw [h9]
    rw [h1]
    nlinarith [sq_nonneg (sin (2 * a * x + b + c) - sin (b - c)), sq_nonneg (sin (2 * a * x + b + c) + sin (b - c)), 
      Real.sin_le_one (2 * a * x + b + c), Real.sin_le_one (b - c), Real.neg_one_le_sin (2 * a * x + b + c), Real.neg_one_le_sin (b - c)]
  
  · -- Proof of the upper bound
    rw [h2]
    rw [h1]
    nlinarith [sq_nonneg (sin (2 * a * x + b + c) - sin (b - c)), sq_nonneg (sin (2 * a * x + b + c) + sin (b - c)), 
      Real.sin_le_one (2 * a * x + b + c), Real.sin_le_one (b - c), Real.neg_one_le_sin (2 * a * x + b + c), Real.neg_one_le_sin (b - c)]