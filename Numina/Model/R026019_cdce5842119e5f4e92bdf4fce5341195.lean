import Mathlib

theorem algebra_2250 {x y : ℝ} (h1 : x ^ 2 + 3 * x * y = 54) (h2 : x * y + 4 * y ^ 2 = 115) :
    (x, y) = (-3, -5) ∨ (x, y) = (3, 5) ∨ (x, y) = (-36, 23 / 2) ∨ (x, y) = (36, -23 / 2) := by
  have h3 : (x + 2 * y) ^ 2 = 169 := by
    nlinarith
  have h4 : x + 2 * y = 13 ∨ x + 2 * y = -13 := by 
    have h3' : (x + 2 * y) ^ 2 - 169 = 0 := by linarith
    have h3'' : (x + 2 * y - 13) * (x + 2 * y + 13) = 0 := by nlinarith 
    cases' (mul_eq_zero.1 h3'') with h5 h6 
    · -- x + 2y - 13 = 0 
      left 
      linarith 
    · -- x + 2y + 13 = 0 
      right 
      linarith 
  cases h4 with
  | inl h4 =>
    have hx1 : x = 13 - 2 * y := by linarith 
    rw [hx1] at h1 h2 
    have h5 : 2 * y ^ 2 + 13 * y - 115 = 0 := by 
      nlinarith 
    have h6 : (y - 5) * (y + 23 / 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h6) with hy1 hy2 
    · -- y = 5 
      have hy : y = 5 := by linarith 
      have hx : x = 3 := by 
        linarith [hx1, hy] 
      right 
      left 
      simp [hx, hy]
    · -- y = -23/2 
      have hy : y = -23 / 2 := by linarith 
      have hx : x = 36 := by 
        linarith [hx1, hy] 
      right 
      right 
      right 
      simp [hx, hy]
  | inr h4 =>
    have hx2 : x = -13 - 2 * y := by linarith 
    rw [hx2] at h1 h2 
    have h7 : 2 * y ^ 2 - 13 * y - 115 = 0 := by 
      nlinarith 
    have h8 : (y - 23 / 2) * (y + 5) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h8) with hy1 hy2 
    · -- y = 23/2 
      have hy : y = 23 / 2 := by linarith 
      have hx : x = -36 := by 
        linarith [hx2, hy] 
      right 
      right 
      left 
      simp [hx, hy]
    · -- y = -5 
      have hy : y = -5 := by linarith 
      have hx : x = -3 := by 
        linarith [hx2, hy] 
      left 
      simp [hx, hy]