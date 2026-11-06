import Mathlib

/- If the radius of a circle is a rational number, its area is given by a number which is:
(A) rational (B) irrational (C) integral (D) a perfect square (E) none of these -/
theorem number_theory_94105 (r : ℚ) (hr : r > 0) :
    -- The area of a circle with radius r is πr^2
    Irrational (Real.pi * r ^ 2) := by 
  norm_cast
  -- Multiplying an irrational number by a nonzero rational number gives an irrational number
  apply Irrational.mul_rat 
  -- Pi is irrational
  exact irrational_pi 
  -- r^2 is nonzero, as it is bigger than zero
  simp; exact hr.ne.symm