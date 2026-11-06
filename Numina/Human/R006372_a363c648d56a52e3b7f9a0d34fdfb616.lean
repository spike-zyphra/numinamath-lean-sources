import Mathlib
/- Let $a, b, c$ be integers and let $X$ be an integer such that $ab + bc + ca = X$. Show that the product $(X+ a^2 )(X+ b^2 )(X+ c^2 )$ is a perfect square, namely the square of $(a+b)(b+c)(c+a)$. -/
theorem algebra_636388 (a b c X : ℤ) (hX : X = a * b + b * c + c * a) : (X + a ^ 2) * (X + b ^ 2) * (X + c ^ 2) = ((a + b) * (b + c) * (c + a)) ^ 2:= by
  -- Substitute X with a * b + b * c + c * a
  subst X
  -- Expand the expression
  linarith
