import Mathlib

/- Prove, if $x^2+y=y^2+z=z^2+x$, then $$x^3+y^3+z^3=xy^2+yz^2+zx^2$$ -/
theorem algebra_26457 {x y z : ℝ} (h : x^2 + y = y^2 + z ∧ y^2 + z = z^2 + x) :
    x^3 + y^3 + z^3 = x * y^2 + y * z^2 + z * x^2 := by 
  ring_nf at *
  nlinarith