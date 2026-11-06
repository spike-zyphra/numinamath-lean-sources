import Mathlib

theorem algebra_285465 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x / 3 = y ^ 2) (h2 : x / 9 = 9 * y) : x + y = 2214 := by
  have eqn1 : x = 3 * y ^ 2 := by
    field_simp at h1 
    linarith 
  have eqn2 : x = 81 * y := by 
    field_simp at h2 
    nlinarith 
  have eqn3 : 3 * y ^ 2 = 81 * y := by 
    linarith [eqn1, eqn2]
  have h3 : y = 27 := by
    have eqn4 : 3 * y ^ 2 - 81 * y = 0 := by linarith [eqn3]
    have eqn5 : 3 * y * (y - 27) = 0 := by
      linarith [eqn4]
    cases' (mul_eq_zero.mp eqn5) with h4 h5
    · -- Case 3 * y = 0 
      have h4' : y = 0 := by
        nlinarith 
      contradiction 
    · -- Case y - 27 = 0 
      linarith 
  have h4 : x = 2187 := by 
    rw [show y = 27 by linarith [h3]] at eqn1 
    nlinarith 
  linarith [h4, h3]