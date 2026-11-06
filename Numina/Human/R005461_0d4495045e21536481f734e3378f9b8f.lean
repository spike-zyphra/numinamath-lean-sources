import Mathlib
/- Given that three roots of $f(x)=x^{4}+a x^{2}+b x+c$ are $2,-3$, and 5 , what is the value of $a+b+c$ ? -/
theorem algebra_608385 (f : ℝ → ℝ) (hf : f = fun x => x ^ 4 + a * x ^ 2 + b * x + c) (h1 : f 2 = 0) (h2 : f (-3) = 0) (h3 : f 5 = 0) : a + b + c = 79:= by
  -- Simplify the function definition in all three equations
  simp [hf] at h1 h2 h3
  -- Normalize the ring expressions in all three equations
  ring_nf at h1 h2 h3
  -- Solve the system of linear equations to get a + b + c = 79
  linarith
