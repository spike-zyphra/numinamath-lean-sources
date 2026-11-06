import Mathlib

/- There exist real numbers x and y, both greater than 1,
such that log_x(y^x)=10 and log_y(x^(4*y))=10.
Find x*y. -/

theorem algebra_93083 {x y : ℝ} (hx : x > 1) (hy : y > 1)
(h₁ : Real.logb x (y ^ x) = 10) (h₂ : Real.logb y (x ^ (4 * y)) = 10) :
x * y = 25 := by
  -- let's simplify h₁ and h₂
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by linarith)] at h₁
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by linarith)] at h₂
  -- multiply the equations together and simplify
  have h3 :=
    calc 100
    _ = (10*10:ℝ) := by norm_num
    _ = x * Real.logb x y * 4 * y * Real.logb y x := by rw [h₁, mul_assoc 10, mul_assoc, h₂];
    _ = x * 4 * y * (Real.logb x y * Real.logb y x) := by ring_nf
    _ = x * 4 * y * 1 := by rw [← Real.inv_logb x, mul_inv_cancel₀ (by simp; refine ⟨by linarith, ⟨by linarith, ⟨by linarith, ⟨by linarith, ⟨by linarith, by linarith⟩⟩⟩⟩⟩)]
    _ = 4*x*y := by ring_nf
  -- trivial now
  linarith