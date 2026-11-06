import Mathlib

theorem algebra_9207 (f : ℝ → ℝ) (hf : f = fun x => x^3 - 3 * x^2 + 4) :
    StrictAntiOn f (Set.Ioo 0 2) := by
  intro x hx y hy hxy
  have h1 : 0 < x := hx.1
  have h2 : x < 2 := hx.2
  have h3 : 0 < y := hy.1
  have h4 : y < 2 := hy.2
  have hfx : f x = x^3 - 3 * x^2 + 4 := by
    rw [hf]
  have hfy : f y = y^3 - 3 * y^2 + 4 := by
    rw [hf]
  rw [hfx, hfy]
  have h5 : x < y := hxy
  have h6 : x^3 - 3 * x^2 + 4 > y^3 - 3 * y^2 + 4 := by
    have h7 : x^3 - 3 * x^2 > y^3 - 3 * y^2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), 
          mul_pos (show (0 : ℝ) < 2 - x by linarith) (show (0 : ℝ) < 2 - y by linarith), 
          mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith), 
          mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < 2 - x by linarith), 
          mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < 2 - y by linarith)
        ]
    linarith
  linarith