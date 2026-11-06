import Mathlib 

/-Montrer que l'équation

$$
x(x+2)=y(y+1)
$$

n'a pas de solution en nombres entiers strictement positifs.-/
theorem number_theory_108637 (x y : ℤ) (hx : x > 0) (hy : y > 0) : 
  ¬ x * (x + 2) = y * (y + 1) := by 
    intro h 
    -- We have equation that x(x+2) = y(y+1), i.e. x^2 + 2*x = y^2 + y.
    -- So $x < y$, otherwise $y^2 ≤ x^2$ and $y < 2x$, which contradicts with x^2 + 2*x = y^2 + y.
    have h1 : x < y := by nlinarith
    -- Rearrange the equation we get $(x+1)^2 = y^2 + y + 1$. Because $y + 1$ is positive, $y < x + 1$.
    have h2 : y < x + 1 := by nlinarith 
    -- There is a contradiction in inequalities.
    omega