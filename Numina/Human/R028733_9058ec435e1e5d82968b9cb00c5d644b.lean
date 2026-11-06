import Mathlib
/- Calculate the sum of the coefficients of $P(x)$ if $\left(20 x^{27}+2 x^{2}+1\right) P(x)=2001 x^{2001}$. -/
theorem algebra_610841 (P : ℝ → ℝ) (h : ∀ x : ℝ, (20 * x ^ 27 + 2 * x ^ 2 + 1) * P x = 2001 * x ^ 2001) : P 1 = 87:= by
  -- use 1 in h
  specialize h 1
  -- simp the expression
  simp at h
  -- use linarith to finish the proof
  linarith
