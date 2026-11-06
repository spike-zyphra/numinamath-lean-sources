import Mathlib

theorem algebra_253677 {x y z : ℝ} (h1 : x * (1 + y * z) = 9) (h2 : y * (1 + x * z) = 12)
    (h3 : z * (1 + x * y) = 10) :
    x = 1 ∧ y = 4 ∧ z = 2 := by

  have eq1 : x + x * y * z = 9 := by linarith
  have eq2 : y + x * y * z = 12 := by linarith
  have eq3 : z + x * y * z = 10 := by linarith
  
  have h4 : y - x = 3 := by nlinarith [eq1, eq2]
  have h5 : z - x = 1 := by nlinarith [eq1, eq3]

  have hy : y = x + 3 := by linarith
  have hz : z = x + 1 := by linarith
  
  rw [hy, hz] at h1
  
  have h6 : x^3 + 4 * x^2 + 4 * x - 9 = 0 := by
    ring_nf at h1
    linarith
  
  have h7 : (x - 1) * (x^2 + 5 * x + 9) = 0 := by
    ring_nf at h6 ⊢
    nlinarith
  
  cases' (mul_eq_zero.mp h7) with h8 h9
  
  · -- Case where x - 1 = 0, thus x = 1
    have hx : x = 1 := by linarith
    have hy4 : y = 4 := by
      rw [hx] at hy
      linarith
    have hz2 : z = 2 := by
      rw [hx] at hz
      linarith
    exact ⟨hx, hy4, hz2⟩

  · -- Case where x^2 + 5x + 9 = 0, show that it's impossible
    have h10 : x^2 + 5 * x + 9 > 0 := by
      nlinarith [sq_nonneg (x + 5 / 2)]
    
    have h11 : x^2 + 5 * x + 9 = 0 := by 
      linarith
    
    linarith [h10, h11]