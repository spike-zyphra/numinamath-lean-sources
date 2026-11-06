import Mathlib

/- Prove that $$x^2 +\frac{8}{xy}+ y^2 \ge 8$$ for all positive real numbers $x$ and $y$. -/
theorem inequalities_62960 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^2 + 8 / (x * y) + y^2 ≥ 8 := by
  have h₀ : 0 < x * y := mul_pos hx hy
  field_simp
  rw [le_div_iff h₀]
  nlinarith [hx, hy, sq_nonneg (x - y), sq_nonneg (x * y - 2)]
  <;> nlinarith [hx, hy, sq_nonneg (x - y), sq_nonneg (x * y - 2)]