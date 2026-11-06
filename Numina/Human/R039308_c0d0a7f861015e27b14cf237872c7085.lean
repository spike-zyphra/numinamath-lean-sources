import Mathlib

open Real

/-
Let $S=\sqrt{1+\frac{1}{1^{2}}+\frac{1}{2^{2}}}+$ $\sqrt{1+\frac{1}{2^{2}}+\frac{1}{3^{2}}}+\cdots+\sqrt{1+\frac{1}{1999^{2}}+\frac{1}{2000^{2}}}$. Find the greatest integer $[S]$ not exceeding $S$.
-/
theorem algebra_302428 :
    ⌊∑ i ∈ Finset.range 1999, sqrt (1 + 1 / (i + 1)^2 + 1 / (i + 2)^2)⌋ = 1999 - 1 / 2000 := by
  have h : ∀ i : ℕ, √(1 + 1 / (i + 1) ^ 2 + 1 / (i + 2) ^ 2 : ℝ) = 1 + 1 / ((i + 1) * (i + 2)) := by
    intro i
    have h1 : (1 : ℝ) + 1 / (i + 1) ^ 2 + 1 / (i + 2) ^ 2 = (1 + 1 / ((i + 1) * (i + 2))) ^ 2 := by
      field_simp
      ring
    rw [h1]
    rw [Real.sqrt_sq]
    positivity
  simp_rw [h]
  norm_num [Finset.sum_range_succ, Int.floor_eq_iff]
