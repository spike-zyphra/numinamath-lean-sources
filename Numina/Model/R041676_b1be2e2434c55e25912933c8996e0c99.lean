import Mathlib

theorem algebra_243905 {x y z : ℝ} (h1 : x + y + z = 13) (h2 : x^2 + y^2 + z^2 = 61) (h3 : x * y + x * z = 2 * y * z) :
    (x = 4 ∧ y = 3 ∧ z = 6) ∨ (x = 4 ∧ y = 6 ∧ z = 3) := by 
  have eq1 : y + z = 13 - x := by linarith 
  have eq2 : x * (y + z) = 2 * y * z := by 
    linarith 
  rw [eq1] at eq2 
  have eq3 : x^2 + (y + z)^2 - 2 * (y * z) = 61 := by 
    nlinarith 
  rw [eq1] at eq3 
  have eq4 : x^2 + (13 - x)^2 - x * (13 - x) = 61 := by 
    nlinarith [eq2] 
  have h4 : (x - 4) * (x - 9) = 0 := by 
    ring_nf at eq4 ⊢
    linarith 
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case x = 4
    have hx : x = 4 := by linarith 
    have eq5 : y + z = 9 := by 
      rw [hx] at eq1 
      linarith 
    have eq6 : y * z = 18 := by 
      rw [hx] at eq2 
      nlinarith 
    have eq7 : (y - 3) * (y - 6) = 0 := by 
      nlinarith [sq_nonneg (y - 3), sq_nonneg (y - 6), eq5, eq6] 
    cases' (mul_eq_zero.1 eq7) with h8 h9
    · -- Case y = 3 
      have hy : y = 3 := by linarith 
      have hz : z = 6 := by linarith 
      left 
      exact ⟨by linarith, by linarith, by linarith⟩ 
    · -- Case y = 6 
      have hy : y = 6 := by linarith 
      have hz : z = 3 := by linarith 
      right 
      exact ⟨by linarith, by linarith, by linarith⟩ 
  · -- Case x = 9 
    have hx : x = 9 := by linarith 
    have eq5 : y + z = 4 := by 
      rw [hx] at eq1 
      linarith 
    have eq6 : y * z = 18 := by 
      rw [hx] at eq2 
      nlinarith 
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 4)]