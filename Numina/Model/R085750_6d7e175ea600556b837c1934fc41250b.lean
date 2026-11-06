import Mathlib

theorem algebra_4964 :
  IsGreatest {n : ℕ | ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 5 * x + 3 * y = 69 ∧ n = x * y} 78 := by 
  constructor
  · -- Prove 78 is achievable by x = 6 and y = 13
    use 6, 13
    all_goals norm_num
  · -- Prove that any n in the set is at most 78
    intro n hn
    rcases hn with ⟨x, y, hx_pos, hy_pos, h_eq, heq⟩
    have h1 : x ≤ 13 := by 
      omega -- Solving inequality: 5 * x + 3 * y = 69 with y > 0 implies x < 14
    have h2 : y ≤ 23 := by
      omega -- Solving inequality: 5 * x + 3 * y = 69 with x > 0 implies y < 24
    interval_cases x <;> omega -- Solving finite arithmetic
    <;> try { 
      nlinarith -- Solving the constraints to maximize n
    }
    <;> nlinarith -- Solving the constraints to maximize n even after 2 steps
    <;> tauto -- Trying to solve the implication if we need it