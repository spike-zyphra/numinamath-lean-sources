import Mathlib

/--man_cnt denote the number of men excepts Peter. -/
def man_cnt := 49
/-- woman_cnt denote the number of women.-/
def woman_cnt := 50

/-- The proportion of men excepts Peter in all excepts Peter. -/
def p_peter_left_is_man : ℚ := man_cnt / (man_cnt + woman_cnt)

/-- the possibility of Peter is not satisfied. -/
def p_peter_left_is_man_and_right_is_man : ℚ :=
  p_peter_left_is_man * (man_cnt - 1) / (man_cnt + woman_cnt - 1)

/-- the possibility of Peter is satisfied. -/
def p_peter_satisfied : ℚ := 1 - p_peter_left_is_man_and_right_is_man

/-- 
a) : Peter Ivanovich, along with 49 other men and 50 women, are seated in a random order around a round table. We call a man satisfied if a woman is sitting next to him. Find the probability that Peter Ivanovich is satisfied. -/
theorem combinatorics_4040_a : p_peter_satisfied = (25:ℚ) / 33 := by
  rw [p_peter_satisfied, p_peter_left_is_man_and_right_is_man, p_peter_left_is_man, man_cnt, woman_cnt]
  ring

/-- the possibility of one man is satisfied. -/
def p_one_man_is_satisfied : ℚ := p_peter_satisfied

def e_number_of_satisfied_man : ℚ := (1 + man_cnt) * p_one_man_is_satisfied

/-
 b) : Peter Ivanovich, along with 49 other men and 50 women, are seated in a random order around a round table. We call a man satisfied if a woman is
sitting next to him. Find the expected number of satisfied men.
-/
theorem combinatorics_4040_b : e_number_of_satisfied_man = (1250:ℚ) / 33 := by
  rw [e_number_of_satisfied_man, man_cnt, p_one_man_is_satisfied, combinatorics_4040_a]
  ring
