import Mathlib

theorem algebra_114 {a b c : ℝ} (habc : a * b * c ≠ 0) (h : a + b + c = 0) :
    a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = 3 := by

  have h1 : a ≠ 0 := by
    by_contra ha
    have : a * b * c = 0 := by
      rw [ha]
      norm_num
    contradiction

  have h2 : b ≠ 0 := by
    by_contra hb
    have : a * b * c = 0 := by
      rw [hb]
      norm_num
    contradiction
  
  have h3 : c ≠ 0 := by
    by_contra hc
    have : a * b * c = 0 := by
      rw [hc]
      norm_num
    contradiction
  
  have eq1 : a ^ 2 / (b * c) + b ^ 2 / (c * a) + c ^ 2 / (a * b) = (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by 
    field_simp [h1, h2, h3]
    ring

  have h4 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by
    have h5 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      ring_nf
    rw [h] at h5
    have h6 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 0 := by linarith
    linarith
  
  rw [eq1]

  have h8 : a * b * c ≠ 0 := habc
  
  have h7 : (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) = 3 := by
    rw [h4]
    field_simp [h8]
    <;> nlinarith
  
  exact h7