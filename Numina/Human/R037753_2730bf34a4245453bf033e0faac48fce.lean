import Mathlib

/- A company that sells widgets has to pay $\$500$ in maintenance fees each day and then it pays each worker $\$15$ per hour. Each worker makes 5 widgets per hour, which are sold at $\$3.10$ each. What is the least number of workers the company has to hire in order to make a profit in an 8-hour workday? -/
theorem algebra_13883 : IsLeast {n : ℕ | 500 + 8 * 15 * n < (8 * 3.1 * 5 * n : ℝ)} 126 := by
  -- Simplify the inequality to: 125 < x
  have h {x : ℝ} : 500 + 8 * 15 * x < 8 * 3.1 * 5 * x ↔ 125 < x := by
    norm_num
    constructor
    all_goals
      intro h
      linarith

  -- Prove 126 is in the set and it's the least
  constructor
  . simp
    rw [h]
    norm_num

  . intro n hn
    simp at hn
    rw [h] at hn
    norm_cast at hn
