import Mathlib

theorem algebra_144460 {x y z : ℝ} (h1 : (x - 1)/8 = (y - 8)/(-5)) (h2 : (y - 8)/(-5) = (z + 5)/12)
    (h3 : x - 2*y - 3*z + 18 = 0) :
    x = 9 ∧ y = 3 ∧ z = 7 := by
  have eq1 : -5 * x - 8 * y + 69 = 0 := by
    field_simp at h1
    linarith
  -- Cross-multiplication and simplification of h2
  have eq2 : 12 * y + 5 * z - 71 = 0 := by
    field_simp at h2
    linarith
  have hx : x = 9 := by 
    nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 3), sq_nonneg (z - 7), 
      sq_nonneg (x -9), sq_nonneg (y -3), sq_nonneg (z -7)]
  -- Prove y and z after proving x
  have hy : y = 3 := by
    nlinarith [sq_nonneg (y - 3), sq_nonneg (z - 7), hx]
  -- Prove z after proving x and y
  have hz : z = 7 := by 
    nlinarith [sq_nonneg (z - 7), hy]
  exact ⟨hx, hy, hz⟩