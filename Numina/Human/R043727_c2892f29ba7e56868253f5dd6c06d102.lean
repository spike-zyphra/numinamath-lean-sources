import Mathlib

/- 5. Let the even function $f(x)$ satisfy: $f(1)=2$, and when $x y \neq 0$, $f\left(\sqrt{x^{2}+y^{2}}\right)=\frac{f(x) f(y)}{f(x)+f(y)}$. Then $f(5)=$ $\qquad$. -/
theorem algebra_198250 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x) (h₁ : f 1 = 2)
    (h₂ : ∀ x y, x * y ≠ 0 → f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y / (f x + f y)) :
    f 5 = 2 / 25 := by

  -- notice that 1 / f √(x^2+y^2) = 1 / fx + 1 / fy
  have hf1 {x y: ℝ} (hxy: x*y ≠ 0) (hx: f x ≠ 0) (hy: f y ≠ 0):
    1 / f (√(x^2+y^2)) = 1 / f x + 1 / f y := by
    rw [h₂ x y hxy, one_div_div]
    field_simp [hx, hy]
    ring

  -- by induction, 1 / f(√k) = k 1 / f(1) for natural number k.
  have hf2 {k:ℕ} (hk: k ≥ 1): 1 / f √k = k * (1 / f 1) := by
    induction' k,hk using Nat.le_induction with k hk ih
    · simp
    · push_cast
      have: √(k+1) = √((√k)^2 + 1^2) := by
        congr 1
        simp only [Nat.cast_nonneg, Real.sq_sqrt, one_pow]
      nth_rw 1 [this]
      have h1: √k * 1 ≠ 0 := by
        simp only [mul_one, ne_eq, Nat.cast_nonneg,
        Real.sqrt_eq_zero, Nat.cast_eq_zero]
        exact Nat.not_eq_zero_of_lt hk
      have h2: f √k ≠ 0 := by
        rintro heq
        simp [heq, h₁, Nat.not_eq_zero_of_lt hk] at ih
      have h3: f 1 ≠ 0 := by simp [h₁]
      rw [hf1 h1 h2 h3, ih]
      ring

  -- therefore 1 / f (√25) = 25 / f1 = 25 / 2
  have h1: 5^2 ≥ 1 := by norm_num
  have h2: √(↑(5^2:ℕ)) = 5 := by
    push_cast
    have: (25:ℝ) = 5^2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  specialize hf2 h1
  rw [h2] at hf2
  rw [← one_div_one_div (f 5), hf2, h₁]
  norm_num