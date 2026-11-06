import Mathlib

/- 6.349 Solve the equations $2 x^{3}-5 x^{2}+6 x-2=0$ and $6 x^{3}-3 x^{2}-2 x+1=0$, given that they have a common root. -/
theorem algebra_195540 (x : ℝ) (hx : 2*x^3-5*x^2+6*x-2=0) (hx' : 6*x^3-3*x^2-2*x+1=0) :
    x=1/2 ∨ x=1/Real.sqrt 3 ∨ x=2/Real.sqrt 3 := by 
  apply Or.inl
  apply Eq.symm
  ring_nf at hx'
  nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1 / Real.sqrt 3), sq_nonneg (x - 2 / Real.sqrt 3)]
