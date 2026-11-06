import Mathlib

theorem algebra_223015 {x y : ℝ} (h1 : 2 * y = 4 - x ^ 2) (h2 : 2 * x = 4 - y ^ 2) :
    (x = -1 + Real.sqrt 5 ∧ y = -1 + Real.sqrt 5) ∨
    (x = -1 - Real.sqrt 5 ∧ y = -1 - Real.sqrt 5) ∨
    (x = 0 ∧ y = 2) ∨
    (x = 2 ∧ y = 0) := by
  have h3 : (x - y) * (x + y - 2) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.1 h3) with h4 h5 
  · -- Case x - y = 0, so x = y 
    have h4' : x = y := by linarith 
    have eq1 : 2 * x = 4 - x ^ 2 := by 
      have eq2 : y = x := by linarith [h4'] 
      rw [eq2] at h1 
      linarith 
    have h8 : (x - (-1 + Real.sqrt 5)) * (x - (-1 - Real.sqrt 5)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h8) with h9 h10 
    · -- Case x = -1 + Real.sqrt 5 
      have hx1 : x = -1 + Real.sqrt 5 := by linarith
      have hy1 : y = -1 + Real.sqrt 5 := by linarith [h4', hx1]
      left 
      exact ⟨hx1, hy1⟩
    · -- Case x = -1 - Real.sqrt 5 
      have hx2 : x = -1 - Real.sqrt 5 := by linarith 
      have hy2 : y = -1 - Real.sqrt 5 := by linarith [h4', hx2]
      right 
      left 
      exact ⟨hx2, hy2⟩
  · -- Case x + y - 2 = 0, so x + y = 2
    have h6 : y = 2 - x := by linarith 
    rw [h6] at h1 
    have h7 : x * (x - 2) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h7) with h8 h9 
    · -- Case x = 0 
      have hx1 : x = 0 := by linarith
      have hy1 : y = 2 := by 
        rw [hx1] at h6 
        linarith 
      right 
      right 
      left 
      exact ⟨hx1, hy1⟩ 
    · -- Case x - 2 = 0, so x = 2 
      have hx2 : x = 2 := by linarith 
      have hy2 : y = 0 := by 
        rw [hx2] at h6 
        linarith 
      right 
      right 
      right 
      exact ⟨hx2, hy2⟩