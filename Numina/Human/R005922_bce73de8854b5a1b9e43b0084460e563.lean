import Mathlib

/-Positive integers $a, b$, and $c$ have the property that $a^{b}, b^{c}$, and $c^{a}$ end in 4,2 , and 9 , respectively. Compute the minimum possible value of $a+b+c$.-/
theorem number_theory_610728 : IsLeast {t | ∃ a b c, t = a + b + c ∧ a ^ b % 10 = 4
    ∧ b ^ c % 10 = 2 ∧ c ^ a % 10 = 9} 17 := by
-- Split the goal to an existential subgoal and a lower bound subgoal
  simp [IsLeast, lowerBounds]; constructor
  -- Use 2, 2, 13 to fulfill the goal
  · use 2, 2, 13; norm_num
-- Assume the contrary that the sum of $a$, $b$ and $c$ is less than $17$
  intro t a b c ht h1 h2 h3; rw [ht]; clear ht t
  by_contra!; have : a < 17 := by omega
  have : b < 17 := by omega
  have : c < 17 := by omega
-- Check all possible values of $a$, $b$ and $c$, the goal will follow
  interval_cases a <;> interval_cases b
  all_goals norm_num at h1
  all_goals interval_cases c
  all_goals norm_num at h2
  all_goals norm_num at h3
  norm_num at this