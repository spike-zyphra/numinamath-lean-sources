import Mathlib

theorem algebra_22477 (z1 z2 : ℂ) (hz1 : z1 = 5 + 6 * .I) (hz2 : z2 = -2 + 2 * .I) :
    Complex.abs (z1 - z2) = Real.sqrt 65 := by 
  rw [hz1, hz2]
  simp [Complex.abs, Complex.normSq]
  norm_num