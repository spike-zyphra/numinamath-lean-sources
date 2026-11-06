import Mathlib

/- For all positive real numbers $x$ and $y$ let

$$
f(x, y)=\min \left(x, \frac{y}{x^{2}+y^{2}}\right) .
$$

Show that there exist $x_{0}$ and $y_{0}$ such that $f(x, y) \leqslant f\left(x_{0}, y_{0}\right)$ for all positive $x$ and $y$, and find $f\left(x_{0}, y_{0}\right)$. -/
theorem algebra_605732 (f : ℝ → ℝ → ℝ) (hf : ∀ x y : ℝ, f x y = min x (y / (x^2 + y^2))) :
  ∃ x₀ y₀ : ℝ, x₀ > 0 ∧ y₀ > 0 ∧ (∀ x y : ℝ, x > 0 ∧ y > 0 → f x y ≤ f x₀ y₀) ∧ f x₀ y₀ = 1 / √2 := by
  -- We show that the minimum value is attained at (1 / √2, 1 / √2).
  use 1 / √2, 1 / √2, by positivity, by positivity
  -- Calculate the value of f at (1 / √2, 1 / √2).
  have hmax : f (1 / √2) (1 / √2) = 1 / √2 := by
    simp [hf]
    norm_num
  refine ⟨?_, hmax⟩
  -- Let x, y be positive real numbers.
  rintro x y ⟨hx, hy⟩
  -- It suffices to show that f(x, y) ≤ 1 / √2.
  rw [hmax]
  -- Use the property of the minimum function,
  -- it suffices to show that x ≤ 1 / √2 or y / (x ^ 2 + y ^ 2) ≤ 1 / √2.
  simp [hf, -one_div]
  -- We assume x > 1 / √2, and we show that y / (x ^ 2 + y ^ 2) ≤ 1 / √2.
  by_contra! K
  rcases K with ⟨K₁, K₂⟩
  absurd K₂
  clear K₂
  push_neg
  calc y / (x ^ 2 + y ^ 2)
    -- x ^ 2 + y ^ 2 ≥ 2 * x * y
    _ ≤ y / (2 * x * y) := by
      rw [div_le_div_iff_of_pos_left (by positivity) (by positivity) (by positivity)]
      exact two_mul_le_add_sq x y
    _ = 1 / (2 * x) := by
      field_simp
      ring
    _ ≤ 1 / √2 := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      rw [← show √2 / 2 = 1 / √2 from Real.sqrt_div_self'] at K₁
      linarith only [K₁]
