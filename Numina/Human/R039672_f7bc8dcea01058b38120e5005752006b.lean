import Mathlib
open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/-
Example 15 (2006 Girls' Mathematical Olympiad, adapted) Let $a>0$, and let $f:(0,+\infty) \rightarrow \mathbf{R}$ be a continuous function, satisfying $f(a)=1$. If for any $x, y \in \mathbf{R}^{+}$, we have $f(x) f(y)+f\left(\frac{a}{x}\right) f\left(\frac{a}{y}\right) \leqslant 2 f(x y)$.
Prove: $f(x) f(y) \leqslant f(x y)$.
-/
theorem inequalities_202276
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < a)
  (_ : ContinuousOn f (Set.Ioi 0))
  (h₂ : f a = 1)
  (h₃ : ∀ x y : ℝ, 0 < x → 0 < y → f x * f y + f (a / x) * f (a / y) ≤ 2 * f (x * y)) :
  ∀ x y : ℝ, 0 < x → 0 < y → f x * f y ≤ f (x * y) := by

  -- First consider the special case x = y = 1. Since f(a) = 1, we can deduce that f(1) = 1.
  have h1 := h₃ 1 1 (by norm_num) (by norm_num)
  norm_num [h₂] at h1
  have h1_eq : f 1 = 1 := by nlinarith [sq_nonneg (f 1 - 1)]

  -- Prove a key property: for any positive x, f(a/x) ≤ f(x)
  have h4 : ∀ x > 0, f (a / x) ≤ f x := by
    intros x hx
    have h := h₃ x 1 (by linarith) (by norm_num)
    simp [h1_eq, h₂] at h
    linarith

  -- Similarly, prove that for any positive y, f(a/y) ≤ f(y)
  have h5 : ∀ y > 0, f (a / y) ≤ f y := by
    intros y hy
    have h := h₃ 1 y (by norm_num) (by linarith)
    simp [h1_eq, h₂] at h
    linarith

  -- Since f(a/x) ≤ f(x) and f(x) = f(a/(a/x)) ≤ f(a/x), we have for any positive x, f(a/x) = f(x)
  have h6 : ∀ x > 0, f (a / x) = f x := by
    intro x hx
    have h4' := h4 x hx
    have h7 : f x ≤ f (a / x) := by
      specialize h4 (a / x) (by
        apply div_pos
        linarith
        linarith
      )
      rw [show a / (a / x) = x by field_simp] at h4
      linarith
    linarith

  -- Substitute f(a/x) = f(x) and f(a/y) = f(y) into the original inequality, we can obtain 2f(x)f(y) ≤ 2f(xy)
  -- Therefore f(x)f(y) ≤ f(xy)
  intros x y hx hy
  have h := h₃ x y (by linarith) (by linarith)
  rw [h6 x (by linarith), h6 y (by linarith)] at h
  linarith
