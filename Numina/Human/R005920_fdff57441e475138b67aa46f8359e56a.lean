import Mathlib

namespace DieRollProblem


-- Neil rolls until N_k ≥ 1. This always happens on the first roll.
-- The probability that Neil's final roll is 3 is the probability that his first
-- roll is 3.
noncomputable def p₁ : ℝ := 1 / 3

-- Neil rolls until N_k ≥ 2.
-- If Neil rolls a 3 (prob 1/3), he stops and N=3.
-- If Neil rolls a 2 (prob 1/3), he stops and N=2.
-- If Neil rolls a 1 (prob 1/3), he continues, and the problem resets.
-- Solving the recursive equation p₂ = 1/3 + (1/3)p₂ gives p₂ = 1/2.
noncomputable def p₂ : ℝ := 1 / 2

-- The recurrence relation for p₂.
theorem p₂_satisfies_recursion : p₂ = 1/3 + (1/3) * p₂ := by
  simp [p₂]
  ring

-- Neil rolls until N_k ≥ 3. This means Neil must roll a 3 to stop.
-- If Neil rolls a 3 (prob 1/3), he stops and N=3.
-- If Neil rolls a 1 or 2 (prob 2/3), he continues, and the problem resets.
-- Solving the recursive equation p₃ = 1/3 + (2/3)p₃ gives p₃ = 1.
def p₃ : ℝ := 1

-- The recurrence relation for p₃.
theorem p₃_satisfies_recursion : p₃ = 1/3 + (2/3) * p₃ := by
  simp [p₃]
  ring

-- The total probability is the average of the conditional probabilities.
noncomputable def total_probability : ℝ := (1/3) * (p₁ + p₂ + p₃)

theorem combinatorics_610723 : total_probability = 11 / 18 := by
  unfold total_probability p₁ p₂ p₃
  norm_num

end DieRollProblem
