import Mathlib

/- A worker receives an annual wage of $\$20{,}000$, which he always deposits into a savings account at the end of the year. By the end of the third year (when he makes the third deposit), he wants to have at least $\$66,200$ in the account to finance the purchase of a house. What is the minimal compound interest rate that the savings account must provide? Express your answer as a percentage, but do not include the percent sign. -/
theorem algebra_20809 {wage price : ℝ} (h1 : wage = 20000) (h2 : price = 66200) : IsLeast {rate : ℝ | 0 < rate ∧ wage * (1 + rate / 100) ^ 2 + wage * (1 + rate / 100) + wage ≥ price} 10 := by
  constructor
  -- $10$ is a possible value
  norm_num [h1, h2]
  -- $10$ is the least such
  intro rate ratein
  rcases ratein with ⟨hr, hge⟩
  rw [h1, h2] at hge
  have le : 0 ≤ 20000 * (1 + rate / 100) ^ 2 + 20000 * (1 + rate / 100) + 20000 - 66200 := by
    linarith
  ring_nf at le
  have eq : -6200 + rate * 600 + rate ^ 2 * 2 = 2 * (rate - 10) * (rate + 310) := by
    ring
  rw [eq] at le
  nlinarith