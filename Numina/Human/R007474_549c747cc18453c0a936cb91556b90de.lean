import Mathlib
open Real

/-
Let $a, b, c, n$ be positive real numbers such that $\frac{a+b}{a}=3, \frac{b+c}{b}=4$, and $\frac{c+a}{c}=n$. Find $n$.
-/
theorem algebra_609891 (a b c n: ℝ)
  (h01: a > 0) (h02: b > 0) (h03: c > 0) (h04: n > 0)
  (h1: (a+b)/a = 3) (h2: (b+c)/b = 4) : ((c+a)/c = 7/6) := by
  -- We first rewrite each condition
  have h1': b/a = 2 := by
    calc
      _ = (b+a)/a - 1 := by field_simp
      _ = 2 := by rw [add_comm, h1]; linarith
  have h2' : c/b = 3 := by
    calc
      _ = (b+c)/b - 1 := by field_simp
      _ = 3 := by rw [h2]; linarith

  -- The core identity to use
  have h: a/c * (c/b) * (b/a) = 1 := by field_simp
  rw [h1', h2'] at h
  have h' : a/c = 1/6 := by linarith
  calc
    _ = a/c + 1 := by field_simp; linarith
    _ = 7/6 := by rw [h']; linarith
