import Mathlib

open Real

theorem algebra_19902 (A B : ℝ) (hA : A = 12) (hB : B = 22) :
    (π * (A / 2)^2) / (π * (B / 2)^2) = 36 / 121 := by 
  rw [hA, hB]
  field_simp [Real.pi_ne_zero]
  <;> ring_nf <;> norm_num