import Mathlib

open Real Set
open scoped BigOperators

/-Compute the domain of the real-valued function \[f(x)=\sqrt{1-\sqrt{2-\sqrt{x}}}.\]-/
theorem algebra_21118  :
    {x : ℝ | 0 ≤ x ∧ 0 ≤ 1 - √(2 - √x) ∧ 0 ≤ 2 - √x } = Set.Icc 1 4 := by
  ext x
  simp
  constructor
  · -- For the contents of the innermost square root to be nonnegative, we must have $x\geq 0$.  To satisfy the middle square root, we must have  $$2-\sqrt{x}\geq 0\Rightarrow 4\geq x.$$ Finally, the outermost square root requires $$1-\sqrt{2-\sqrt{x}}\geq 0.$$ This gives us $$1\geq 2-\sqrt{x}\Rightarrow x\geq 1.$$ Combining our inequalities, we get ${1\leq x\leq 4}$, or $x \in \boxed{[1, 4]}$ in interval notation.
    rintro ⟨hx₁, hx₂⟩
    have hx₁: 1 ≤ √x := by linarith
    rw [le_sqrt' (by positivity)] at hx₁
    rw [sqrt_le_iff] at hx₂
    ring_nf at hx₁ hx₂
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hx₁, hx₂⟩
    constructor
    · have hx₁: 1 ≤ √x := by
        rw [le_sqrt' (by positivity)]
        linarith
      linarith
    · rw [sqrt_le_iff]
      simp
      refine ⟨?_, by ring_nf; exact hx₂⟩
      rw [←one_add_one_eq_two, add_le_add_iff_left 1]
      exact one_le_sqrt.mpr hx₁
