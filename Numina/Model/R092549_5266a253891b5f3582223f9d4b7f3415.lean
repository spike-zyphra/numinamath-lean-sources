import Mathlib

theorem algebra_265295 (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0)
    (h : ∀ x y z, x > 0 → y > 0 → z > 0 → x > y ∧ y > z → f (x - y + z) = f x + f y + f z - x * y - y * z + x * z) :
    ∀ x > 0, f x = x ^ 2 / 2 := by

  -- First introduce x > 0 to prove the function property
  intro x hx

  -- Prove intermediate result: for all x, z > 0 with x > z: f x + f z = (x^2 + z^2)/2
  have h1 : ∀ x z, x > 0 → z > 0 → x > z → f x + f z = (x ^ 2 + z ^ 2) / 2 := by
    intro x z hx1 hz1 hxy
    have hy1 : x > (x + z) / 2 := by
      nlinarith 
    have hy2 : (x + z) / 2 > z := by
      nlinarith 
    have h2 := h x ((x + z) / 2) z hx1 (show (x + z) / 2 > 0 by nlinarith) hz1 ⟨by linarith [hy1], by linarith [hy2]⟩
    have eq1 : x - (x + z) / 2 + z = (x + z) / 2 := by 
      ring
    rw [eq1] at h2
    linarith 
  -- Create equations with different variables
  have eq3 := h1 x (x / 2) hx (show x / 2 > 0 by nlinarith) (show x > x / 2 by nlinarith)
  have eq4 := h1 (x / 2) (x / 4) (show x / 2 > 0 by nlinarith) (show x / 4 > 0 by nlinarith) (show x / 2 > x / 4 by nlinarith)
  have eq5 := h1 x (x / 4) hx (show x / 4 > 0 by nlinarith) (show x > x / 4 by nlinarith)
  
  -- Now solve these nonlinear equations with constraints from positivity
  nlinarith [eq3, eq4, eq5, sq_nonneg (f x - x ^ 2 / 2), sq_nonneg (f (x / 2) - (x / 2) ^ 2 / 2), sq_nonneg (f (x / 4) - (x / 4) ^ 2 / 2), hf x hx, hf (x / 2) (show x / 2 > 0 by nlinarith), hf (x / 4) (show x / 4 > 0 by nlinarith)]