import Mathlib

/- Given that $$(x+y+z)(xy+xz+yz)=18$$and that $$x^2(y+z)+y^2(x+z)+z^2(x+y)=6$$for real numbers $x$, $y$, and $z$, what is the value of $xyz$? -/
theorem algebra_15741 {x y z : ℝ} (h1 : (x + y + z) * (x * y + x * z + y * z) = 18) (h2 : x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) = 6) :
    x * y * z = 4 := by 
  nlinarith