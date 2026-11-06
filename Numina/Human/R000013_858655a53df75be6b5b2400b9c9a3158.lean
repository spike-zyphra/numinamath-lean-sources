import Mathlib


/-- Given that $\alpha$ and $\beta$ satisfy the equations
$$
\begin{array}{c}
\alpha^{3}-3 \alpha^{2}+5 \alpha-4=0, \\
\beta^{3}-3 \beta^{2}+5 \beta-2=0,
\end{array}
$$
find the value of $\alpha + \beta$.-/
theorem algebra_4025 {a b : ℝ} (ha : a^3-3*a^2+5*a-4=0) (hb : b^3-3*b^2+5*b-2=0) : a+b=2 := by
  let x := a - 1
  let y := b - 1
  -- transform the goal to $x+y=0$.
  rw [← sub_eq_zero, show a + b - 2 = x + y by ring]
  -- replace $a-1$ by $x$ in `ha` and simplify.
  have hx : x^3 + 2*x - 1 = 0 := by rw [← ha]; ring
  -- replace $b-1$ by $y$ in `hb` and simplify.
  have hy : y^3 + 2*y + 1 = 0 := by rw [← hb]; ring

  let f : ℝ → ℝ := fun (t : ℝ) => t^3 + 2*t

  -- f is monotonous.
  have f_mono : ∀ x₁ x₂, x₁ < x₂ → f x₁ < f x₂ := by
    intros x y h
    have : f x - f y < 0 := by
      simp only [f]
      calc f x - f y
        _ = (x - y) * ((x + 1/2 * y)^2 + 3/4 * y^2 + 2) := by ring
        _ < 0 := mul_neg_of_neg_of_pos (by linarith)
          (by linarith [pow_two_nonneg (x + 1/2 * y), pow_two_nonneg y])
    linarith
  -- f is injective.
  have f_injective (x₁ x₂ : ℝ) : f x₁ = f x₂ → x₁ = x₂ := by
    intro
    by_cases hlt : x₁ < x₂
    . linarith [f_mono x₁ x₂ hlt]   -- x₁ < x₂
    . by_cases hgt : x₂ < x₁
      . linarith [f_mono x₂ x₁ hgt] -- x₁ > x₂
      . linarith                    -- x₁ = x₂

  -- f is symmetry
  have f_symm (t : ℝ) : f t + f (-t) = 0 := by simp [f]; ring

  -- f x + f y = 0
  have hxy_symm : f x + f y = 0 := by simp [f]; linarith [hx, hy]

  -- x = -y
  have : x = -y := by
    apply f_injective
    linarith [hxy_symm, f_symm y]

  linarith
