  import Mathlib

/- Alec must purchase 14 identical shirts and only has $\$130$. There is a flat $\$2$ entrance fee for shopping at the warehouse store where he plans to buy the shirts.  The price of each shirt is the same whole-dollar amount.  Assuming a $5\%$ sales tax is added  to the price of each shirt, what is the greatest possible price (in dollars) of a  shirt that would allow Alec to buy the shirts? -/
theorem algebra_14094 : IsGreatest {x : ℕ | x * 14 * (1 + 5 / 100 : ℝ) + 2 ≤ 130} 8 := by
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  norm_num
  intro x hx
  -- Prove by contradiction (if x > 8).
  by_contra!
  apply Nat.add_one_le_of_lt at this
  norm_num at this
  have _ : (9 : ℝ) ≤ x := by
    rwa [show (9 : ℝ) = (9 : ℕ) by norm_cast, Nat.cast_le]
  have _ : 126 * (21 / 20 : ℝ) + 2 ≤ 130 := by
    calc
      126 * (21 / 20 : ℝ) + 2 = 9 * 14 * (1 + 5 / 100) + 2 := by norm_num
      _ ≤ x * 14 * (1 + 5 / 100) + 2 := by linarith
      _ ≤ 130 := by assumption
  -- We obtain a contradiction.
  linarith
