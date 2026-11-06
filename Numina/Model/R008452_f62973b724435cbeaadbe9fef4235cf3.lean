import Mathlib

theorem algebra_272828 (total_questions : ℕ) (h : total_questions = 30 + 50)
    (correct_answers_part1 : ℕ) (correct_answers_part2 : ℕ) (total_percentage : ℝ)
    (h1 : correct_answers_part1 = 30 * (70 : ℝ) / 100) (h2 : correct_answers_part2 = 50 * (40 : ℝ) / 100) (h3 : total_percentage = ((correct_answers_part1 : ℝ) + correct_answers_part2) * 100 / (total_questions : ℝ)) : min (min (min (min (|59 - total_percentage|) (|57 - total_percentage|)) (|48 - total_percentage|)) (|51 - total_percentage|)) (|41 - total_percentage|) = |51 - total_percentage| := by
  have ht : (total_questions : ℝ) = (80 : ℝ) := by
    rw [h]
    norm_num
  have h1' : (correct_answers_part1 : ℝ) = (21 : ℝ) := by
    rw [h1]
    norm_num
    <;> linarith
  have h2' : (correct_answers_part2 : ℝ) = (20 : ℝ) := by
    rw [h2]
    norm_num
    <;> linarith
  have h3' : total_percentage = (51.25 : ℝ) := by
    rw [h3]
    rw [h1', h2', ht]
    norm_num
  rw [h3']
  norm_num [abs_of_nonneg, abs_of_nonpos, min_eq_right, min_eq_left]
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> linarith