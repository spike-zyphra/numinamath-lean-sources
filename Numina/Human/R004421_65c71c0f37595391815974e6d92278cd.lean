import Mathlib

/- 2. $g(-x)=(-x)^{3}+(-x)=-x^{3}-x=-\left(x^{3}+x\right)=-g(x)$


$$

f(-x)=g^{3}(-x)-g\left(\frac{1}{-x}\right)-5(-x)^{3}-\frac{1}{-x}=-g^{3}(x)+g\left(\frac{1}{x}\right)+5 x^{3}+\frac{1}{x}=-f(x)

$$


Therefore, $f$ is an odd function $\Rightarrow$ if $x_{0}$ is a root of the original equation, then $-x_{0}$ is also a root of the equation $\Rightarrow$ the sum of the roots is zero, if the roots exist

Check $x=1: g(1)=1^{3}+1=2, g\left(\frac{1}{1}\right)=g(1)=2$, substitute into the original equation: $6=6$ - true $\Rightarrow x=1$ is a root $\Rightarrow$ the roots exist -/
theorem algebra_264377 {f g : ℝ → ℝ}
    (hf : ∀ x, f x = (g x)^3 - g (1 / x) - 5 * x^3 - 1 / x)
    (hg : ∀ x, g x = x^3 + x) :
    Function.Odd f ∧ ∃ x, f x = 0 ∧ f (-x) = 0 := by
  -- show g is odd
  have g_odd : Function.Odd g
  · intro x; rw [hg, hg]; ring
  -- show f is odd
  have f_odd : Function.Odd f
  · intro x
    rw [hf, hf, g_odd x, one_div_neg_eq_neg_one_div x, g_odd (1 / x)]
    ring
  -- use this to show that if x is a root, -x is also a root
  -- so it suffices to show that 1 is a root which is a calculation
  refine ⟨f_odd, 1, ?_⟩
  rw [f_odd, neg_eq_iff_eq_neg, neg_zero, and_self_iff, hf, hg, hg]
  norm_num