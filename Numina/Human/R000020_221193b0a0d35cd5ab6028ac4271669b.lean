import Mathlib

/-- If $\( f(x) = x - 2 \)$, $\( F(x, y) = y^2 + x \)$, and $\( c = F(3, f(b)) \)$, find $\( c \)$.-/
theorem algebra_4032 (c b : ℝ)
  (f : ℝ → ℝ) (F : ℝ → ℝ → ℝ)
  (h_f_def : ∀ x, f x = x - 2)
  (h_F_def : ∀ x y, F x y = y^2 + x)
  (h_f_b : f b = 14)
  (h_c_def : c = F 3 (f b)) :
  c = 199 := by
  simp [h_f_def, h_F_def, h_f_b, h_c_def]
  -- According $f b = b - 2 = 14$, we get $b =16$.
  have h : b = 16 := by
    simp [h_f_def] at h_f_b
    linarith
  -- Substitute $b=16$ into the expression : $$F(3, f(b)) = F(3,14)= 14^2+3$$
  rw [h]
  ring
