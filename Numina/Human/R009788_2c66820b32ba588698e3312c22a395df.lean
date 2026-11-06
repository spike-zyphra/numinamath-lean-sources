import Mathlib

/- The weight of $A$ is $40\%$ greater than the weight of $B$ but $30\%$ less than the weight of $C$. What is the ratio of the weight of $B$ to the weight of $C$ expressed as a common fraction? -/
theorem algebra_19617 {A B C : ℝ} (hne : A ≠ 0) (ha : A = (1 + 40 / 100) * B) (hb : A = (1 - 30 / 100) * C) :
    B / C = 1 / 2 := by
  have Beq : B = A * (10 / 14) := by
    linarith
  have Ceq : C = A * (10 / 7) := by
    linarith
  rw [Beq, Ceq]
  field_simp
  ring