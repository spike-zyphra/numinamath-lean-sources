import Mathlib
inductive Optionn
| A
| B
| C
| D
| E

/-- Define the value of option. -/
def option_value : Optionn → Int
| Optionn.A => 5
| Optionn.B => 1
| Optionn.C => 7/2
| Optionn.D => 17/2
| Optionn.E => 7

/-- The value of $\( 8 - \frac{6}{4 - 2} \)$ is
(A) 5
(B) 1
(C) $\( \frac{7}{2} \)$
(D) $\( \frac{17}{2} \)$
(E) 7-/
theorem algebra_4031 :
  8 - 6 / (4 - 2) = option_value Optionn.A := by
  simp [option_value]
