import Mathlib

theorem algebra_302896 {x y : ℝ} (h : 5*x^2+10*y^2-12*x*y-6*x-4*y+13=0) :
    x=3 ∧ y=2 := by
  have h5 : (y - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - ((6 * y + 3) / 5)), sq_nonneg (y - 2), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (5 * x - 6 * y - 3), sq_nonneg ((y - 2) * (x - 3)), sq_nonneg ((x - (6 * y + 3) / 5) * (y - 2)), sq_nonneg (x -3), sq_nonneg (y - 2)
        ]
  have hy : y = 2 := by 
    nlinarith
  have hx : x = 3 := by 
    rw [hy] at h
    nlinarith 
  exact ⟨hx, hy⟩