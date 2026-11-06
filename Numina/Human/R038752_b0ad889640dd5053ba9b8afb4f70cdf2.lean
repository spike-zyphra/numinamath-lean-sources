import Mathlib

/-Let $S$ be the set of positive real numbers.  Let $f : S \to \mathbb{R}$ be a function such that
\[f(x) f(y) = f(xy) + 2005 \left( \frac{1}{x} + \frac{1}{y} + 2004 \right)\]for all $x,$ $y > 0.$

Let $n$ be the number of possible values of $f(2),$ and let $s$ be the sum of all possible values of $f(2).$  Find $n \times s.$-/
theorem algebra_13061 (f : ℝ → ℝ) (h : ∀ x y, x > 0 → y > 0 → f x * f y = f (x * y) + 2005 * (1 / x + 1 / y + 2004)) : ∃(S : Finset ℝ), S = {z | f 2 = z} ∧ S.card * (∑ z ∈ S, z) = 4011/2 := by
  -- Setting $y = 1,$ we get \[f(x) f(1) = f(x) + \frac{2005}{x} + 2005^2.\]
  use {4011/2}
  have eq₁: ∀x > 0, f x * f 1 = f x + 2005 / x + 2005^2 := by
    intro x hx
    specialize h x 1 hx (by linarith)
    rw [h]
    ring_nf

  -- The value $f(1)$ cannot be 1
  have f1_ne_1 : f 1 ≠ 1 := by
    intro hf1
    specialize eq₁ 1 (by linarith)
    rw [hf1] at eq₁
    linarith

  -- and so we can solve for $f(x)$ to get \[f(x) = \frac{2005/x + 2005^2}{f(1) - 1}.\]
  have eq₂: ∀x > 0, f x = (2005 / x + 2005^2) / (f 1 - 1) := by
    intros x hx
    specialize eq₁ x (by linarith)
    rw [eq_div_iff_mul_eq (sub_ne_zero_of_ne f1_ne_1)]
    linarith

  -- In particular, \[f(1) = \frac{2005 + 2005^2}{f(1) - 1}.\]
  have eq₃: f 1 = (2005 + 2005^2) / (f 1 - 1) := by
    specialize eq₂ 1 (by linarith)
    simp at eq₂
    exact eq₂

  -- Then $f(1)^2 - f(1) - 2005^2 - 2005 = 0,$ which factors as $(f(1) - 2006)(f(1) + 2005) = 0.$
  rw [eq_div_iff_mul_eq (sub_ne_zero_of_ne f1_ne_1)] at eq₃
  have : (f 1 - 2006) * (f 1 + 2005) = 0 := by linarith
  -- Hence, $f(1) = 2006$ or $f(1) = -2005.$
  rcases (mul_eq_zero.mp this) with (r | r)
  . -- If $f(1) = 2006,$ then \[f(x) = \frac{2005/x + 2005^2}{2005} = \frac{1}{x} + 2005.\]
    rw [sub_eq_zero] at r
    have eq₄: ∀x > 0, f x = (2005 / x + 2005^2) / 2005 := by
      intro x hx
      specialize eq₂ x hx
      rw [r] at eq₂
      rw [eq₂]
      ring_nf
    -- We can check that this function works.
    -- Therefore, \[f(x) = \frac{1}{x} + 2005,\]
    have eq₅ : ∀x > 0, f x = 1 / x + 2005 := by
      intro x hx
      specialize eq₄ x hx
      rw [eq₄]
      ring_nf

    -- so $n = 1$ and $s = \frac{1}{2} + 2005 = \frac{4011}{2},$ so $n \times s = \boxed{\frac{4011}{2}}.$
    specialize eq₅ 2 (by linarith)
    simp
    linarith
  . -- If $f(1) = -2005,$ then \[f(x) = \frac{2005/x + 2005^2}{-2006}.\]
    rw [←sub_neg_eq_add, sub_eq_zero] at r
    have eq₄: ∀x > 0, f x = (2005 / x + 2005^2) / -2006 := by
      intro x hx
      specialize eq₂ x hx
      rw [r] at eq₂
      rw [eq₂]
      have : -(2005 : ℝ) - 1 = -2006 := by linarith
      rw [this]
    -- We can check that this function does not work.
    have LHS : ∀ x y, x > 0 → y > 0 → f x * f y = 2005^2 / 2006^2 * (1/x + 2005) * (1/y + 2005) := by
      intro x y hx hy
      rw [eq₄ x hx, eq₄ y hy]
      ring_nf
    have RHS : ∀ x y, x > 0 → y > 0 → f (x * y) + 2005 * (1 / x + 1 / y + 2004)
             = - 2005/2006 * (1/(x * y) + 2005) + 2005 * (1 / x + 1 / y + 2004) := by
      intro x y hx hy
      rw [eq₄ (x * y) (mul_pos hx hy)]
      ring_nf

    specialize h 2 2 (by linarith) (by linarith)
    specialize RHS 2 2 (by linarith) (by linarith)
    specialize LHS 2 2 (by linarith) (by linarith)
    rw [RHS, LHS] at h
    ring_nf at h
    absurd h
    linarith
