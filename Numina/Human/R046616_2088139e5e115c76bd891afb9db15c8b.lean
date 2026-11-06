import Mathlib
open Real

/- Define a function $f$ as follows, which is needed for the problem statement -/
def f  (x : ℝ) := (x^2 + 6*x + 2)^2

/-
Find the minimum possible value of $\left(x^{2}+6 x+2\right)^{2}$ over all real numbers $x$.
-/
theorem algebra_609160 : (∀x, (f x) ≥ 0) ∧ (f (-3+sqrt 7) = 0) ∧ (f (-3+sqrt 7) = 0) := by
  constructor
  -- Prove that $(x^2 + 6*x + 2)^2$ is non-negative for any real number $x$
  intro x
  simp only [f]
  calc
    _ = ((x+3)^2 - 7)^2 := by ring
    _ ≥ 0 := by positivity
  
  -- The minimum 0 is achieved at $(-3+\sqrt{7})$
  simp only [f]; norm_num

  -- The minimum 0 is achieved at $(-3-\sqrt{7})$
  ring_nf; rw [Real.sq_sqrt] <;> linarith
  

