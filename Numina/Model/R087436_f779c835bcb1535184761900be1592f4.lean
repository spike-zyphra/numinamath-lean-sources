import Mathlib

theorem algebra_306207 {x y z : ℝ} (h1 : x * (y + z - x) = 39 - 2 * x ^ 2)
    (h2 : y * (z + x - y) = 52 - 2 * y ^ 2) (h3 : z * (x + y - z) = 78 - 2 * z ^ 2) :
    (x, y, z) = (3, 4, 6) ∨ (x, y, z) = (-3, -4, -6) := by

  have hx : x = 3 ∨ x = -3 := by
    have h : (x - 3) * (x + 3) = 0 := by 
      nlinarith 
    cases (mul_eq_zero.1 h) with
    | inl h1 =>
      left
      linarith
    | inr h2 =>
      right
      linarith

  cases hx with
  | inl hx =>
    have hy : y = 4 := by
      rw [hx] at h1
      nlinarith 
    have hz : z = 6 := by
      rw [hx, hy] at h2
      nlinarith 
    left
    simp [hx, hy, hz]
  
  | inr hx =>
    have hy : y = -4 := by
      rw [hx] at h1
      nlinarith 
    have hz : z = -6 := by
      rw [hx, hy] at h2
      nlinarith 
    right
    simp [hx, hy, hz]