import Mathlib

/-
Find all possible values of $\frac{d}{a}$ where $a^{2}-6 a d+8 d^{2}=0, a \neq 0$.
-/
theorem algebra_609863 {a d : ℝ} (ha : a ≠ 0) (h : a^2 - 6*a*d + 8*d^2 = 0) : (d/a = 1/2 ∨ d/a = 1/4) := by

  -- Since $a \neq 0$, we can safely divide by $a$.
  let x:  ℝ := d / a

  -- Dividing both sides of the equation `a^2 - 6*a*d + 8*d^2 = 0` by `a^2`, we get:
  have h': 1 - 6*x + 8*x^2 = 0 := by
    unfold x
    field_simp
    ring_nf
    have _1: a * d ^ 2 * 8 - a ^ 2 * d * 6 + a ^ 3 = a*(a^2 - 6*a*d + 8*d^2) := by
      ring_nf
    have _2: a^2 - 6*a*d + 8*d^2 = 0 := by
      linarith
    rw [_1]
    rw [_2]
    linarith

  -- Factorize the equation
  have h'': (x-1/2)*(x-1/4) = 0:= by
    field_simp
    linarith

  -- By zero product property,
  have hx: x=1/2 ∨ x=1/4 := by
    apply mul_eq_zero.mp at h''
    rcases h'' with hl | hr
    · left; linarith [hl]
    right; linarith [hr]
  unfold x at hx
  exact hx
    