import Mathlib

open Real Set
open scoped BigOperators

/- 1. Let $f(x)=\mathrm{e}^{2 x}-1, g(x)=\ln (x+1)$. Then the solution set of the inequality $f(g(x))-g(f(x)) \leqslant 1$ is $\qquad$ -/
theorem algebra_186837 {f g : ℝ → ℝ}
  (hf : f = λ x => exp (2 * x) - 1) (hg : g = λ x => log (x + 1)) :
  {x | f (g x) - g (f x) ≤ 1 ∧ x+1>0 ∧ (f x)+1>0} = {x | -1 < x ∧ x ≤ 1} := by
  ext x; simp

  constructor
  · intro h
    obtain ⟨hl, hr1, hr2⟩:= h
    rw [hf, hg] at hl
    simp at hl
    -- we get that f(g(x))-g(f(x)) = x^2
    rw [(by norm_num:(2:ℝ)=1+1), add_mul, Real.exp_add, one_mul, exp_log (by linarith)] at hl
    ring_nf at hl
    have hl':x^2≤ 1 := by linarith
    simp at hl'
    apply abs_le.mp at hl'
    constructor
    linarith
    linarith
  · rintro ⟨h1, h2⟩
    rw [hf, hg]; simp
    -- again same simplification
    rw [(by norm_num:(2:ℝ)=1+1), add_mul, Real.exp_add, one_mul, exp_log (by linarith)]
    ring_nf
    constructor
    suffices x^2≤1 by linarith
    simp
    apply abs_le.mpr
    constructor
    linarith
    linarith
    constructor
    linarith
    exact exp_pos _