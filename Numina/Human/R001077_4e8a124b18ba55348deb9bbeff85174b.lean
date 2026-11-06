import Mathlib

/- If $f(a) = \frac{1}{1-a}$, find the product $f^{-1}(a) \times a \times f(a)$.  (Assume $a \neq 0$ and $a \neq 1$.) -/
theorem algebra_20342 {f : ℝ → ℝ} (hf : ∀ x, f x = 1 / (1 - x)) (a : ℝ) (ha : a ≠ 0 ∧ a ≠ 1) : f.invFun a * a * f a = -1 := by
  -- Substituting $f^{-1}(a)$ into the expression for $f$, we get [f(f^{-1}(a))= \frac{1}{1-f^{-1}(a)}.
  have h1 : f (f.invFun a) = a := by
    apply Function.invFun_eq
    use (1 - 1 / a)
    simp only [one_div, hf, sub_sub_cancel, div_inv_eq_mul, one_mul]
  simp only [hf] at h1
  -- We can now solve for $f^{-1}(a)$ to get $f^{-1}(a) = 1 - \frac{1}{a}$.
  have h2 : f.invFun a = 1 - 1 / a := by
    field_simp [ha.1, ha.2]
    have mid : 1 - f.invFun a ≠ 0 := by
      by_contra contra
      rw [contra] at h1
      simp only [div_zero] at h1
      exact ha.1 h1.symm
    field_simp [mid] at h1
    rw [h1]
    ring
  --So $f^{-1}(a) \times a \times f(a)$ is $$\frac{a-1}{a} \times a \times \frac{1}{1-a} = \boxed{-1}.
  have mid : 1 - a ≠ 0 := by
    intro contra
    apply eq_of_sub_eq_zero at contra
    exact ha.2 contra.symm
  rw [h2, one_div, hf]
  field_simp [ha.1, ha.2, mid]

