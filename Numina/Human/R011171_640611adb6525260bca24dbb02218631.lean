import Mathlib

open Polynomial Complex

/- Let

$$
f(x)=x^{4}-6 x^{3}+26 x^{2}-46 x+65 .
$$

Let the roots of $f(x)$ be $a_{k}+i b_{k}$ for $k=1,2,3,4$. Given that the $a_{k}, b_{k}$ are all integers, find $\left|b_{1}\right|+\left|b_{2}\right|+\left|b_{3}\right|+\left|b_{4}\right|$. -/
theorem algebra_611430 :
    ((X ^ 4 - 6 * X ^ 3 + 26 * X ^ 2 - 46 * X + 65 : ℂ[X]).roots.map (fun x ↦ |x.im|)).sum = 10 := by
  -- We first show the polynomial is of degree 4.
  -- `compute_degree!` is useful for this.
  have hdeg : (X ^ 4 - 6 * X ^ 3 + 26 * X ^ 2 - 46 * X + 65 : ℂ[X]).natDegree = 4 := by compute_degree!
  -- So this polynomial is non-zero.
  have h₀ : (X ^ 4 - 6 * X ^ 3 + 26 * X ^ 2 - 46 * X + 65 : ℂ[X]) ≠ 0 := by
    intro h
    simp [h] at hdeg
  -- We show that 1-2i, 1+2i, 2-3i, 2+3i are roots of this polynomial.
  have H : {1 - 2 * I, 1 + 2 * I, 2 - 3 * I, 2 + 3 * I} ⊆ (X ^ 4 - 6 * X ^ 3 + 26 * X ^ 2 - 46 * X + 65 : ℂ[X]).roots := by
    intro x hx
    simp at hx
    simp [h₀]
    -- Break down powers as multiplications.
    simp [pow_succ]
    -- Four cases to analyze.
    rcases hx with rfl | rfl | rfl | rfl
    all_goals
      -- Calculate the real part and the imaginary part separately.
      simp [Complex.ext_iff]
      -- `norm_num` can prove the equalities of numbers.
      norm_num
  -- There are no duplicate roots, so {1-2i, 1+2i, 2-3i, 2+3i} is a subset of the roots as a multiset.
  rw [← Multiset.le_iff_subset (by norm_num [Complex.ext_iff])] at H
  -- But we know there are at most four roots, so this is an equality.
  apply Multiset.eq_of_le_of_card_le at H
  specialize H (by convert Polynomial.card_roots' _; simp [hdeg])
  -- Finally, we calculate the sum of the absolute values of the imaginary parts.
  norm_num [← H]
