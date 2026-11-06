import Mathlib

theorem algebra_242187 {x y z : ℝ} (h1 : x * y + z = y * z + x) (h2 : y * z + x = z * x + y) :
    x = y ∨ y = z ∨ x = z := by 
  by_cases h : x = z
  · -- Case where x = z
    right
    right
    linarith
  · -- Case where x ≠ z
    have h3 : y = 1 := by
      have h4 : x - z ≠ 0 := by
        intro h5
        apply h
        linarith
      have : y * (x - z) = x - z := by linarith 
      apply (mul_right_inj' h4).mp 
      linarith 
    rw [h3] at h1 h2
    have h4 : (x - 1) * (1 - z) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where x - 1 = 0, so x = 1
      have hx : x = 1 := by linarith 
      left 
      linarith 
    · -- Case where 1 - z = 0, so z = 1
      have hz : z = 1 := by linarith 
      right 
      left 
      linarith