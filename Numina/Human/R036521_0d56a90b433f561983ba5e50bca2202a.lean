import Mathlib

/- What is the ordered pair of real numbers $(x, y)$ which satisfies the equation $|x+ y-7|+ |4x - y+ 12|= 0$? -/
theorem algebra_22183 {x y : ℝ} (h : abs (x + y - 7) + abs (4 * x - y + 12) = 0) :
    (x, y) = (-1, 8) := by
  -- We have a trivial fact: abs x + abs y = 0, then x = y = 0.
  have h₁ : abs (4 * x - y + 12) = 0 := by
    linarith only [h, show abs (x + y - 7) ≥ 0 by positivity, show abs (4 * x - y + 12) ≥ 0 by positivity]
  simp at h₁
  rw [h₁] at h
  simp at h ⊢
  -- We can solve for x and y by linarith.
  refine ⟨by linarith, by linarith⟩
