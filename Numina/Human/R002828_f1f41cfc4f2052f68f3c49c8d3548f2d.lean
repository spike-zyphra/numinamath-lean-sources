import Mathlib

/-- 5. Solve the system of equations
$$
\left\{\begin{array}{l}
x+y=z^{2} \\
y+z=x^{2} \\
z+x=y^{2}
\end{array}\right.
$$ -/
theorem algebra_119177 {x y z : ℝ} (h₀ : x + y = z ^ 2) (h₁ : y + z = x ^ 2)
    (h₂ : z + x = y ^ 2) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 2 ∧ y = 2 ∧ z = 2) := by
  -- Subtracting the second equation from the first, we get x - z = z^2 - x^2,
  have : x - z = z^2 - x^2 := by linarith
  -- that is x - z = (z - x) (z+x).
  have eq1 : x - z = (z - x) * (z + x) := by rw[this]; ring
  -- By assumption, this implies x - z = (z - x) y^2.
  rw[h₂] at eq1
  -- Subtracting the third equation from the second, by similar reasoning
  have : y - x = x^2 - y^2 := by linarith
  have eq2 : y - x = (x - y) * (x + y) := by rw[this]; ring
  -- we get the equation y - x = (x - y)z^2.
  rw[h₀] at eq2
  -- Transform this system to the form (x-z) (1+y^2) = 0, (y-x)*(1+z^2) = 0.
  have eq1' : (x - z) * (1 + y^2) = 0 := by linarith
  have eq2' : (y - x) * (1 + z^2) = 0 := by linarith
  -- Thus it is proven that if the original system has a solution, then x = y = z and 2x=x^2,
  -- since x - z = 0, due to the nonnegativity of the square y^2, and similarly for x - y.
  have xz : x = z := by
    have : 1 + y^2 > 0 := by positivity
    replace this := this.ne
    rw[mul_eq_zero, sub_eq_zero] at eq1'
    tauto
  have xy : x = y := by
    have : 1 + z^2 > 0 := by positivity
    replace this := this.ne
    rw[mul_eq_zero, sub_eq_zero] at eq2'
    tauto
  rcases xz
  rcases xy
  -- Hence x = 0 or x = 2, such that x = y = z = 0 or x = y = z = 2. There are no other solutions
  have eq : x * (x - 2) = 0 := by linarith
  simpa[sub_eq_zero] using eq