import Mathlib



/- Define $E(a,b,c) = a \cdot b^2 + c$. What value of $a$ is the solution to the equation $E(a,4,5) = E(a,6,7)$? -/
theorem algebra_10685 : 
    let E (a b c : ℝ) := a * b ^ 2 + c;
    {a | E a 4 5 = E a 6 7} = {-1 / 10} := by
  intro E
  ext a
  simp_all [E]
  constructor
  all_goals
    intro h
    linarith
