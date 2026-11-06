import Mathlib

theorem algebra_280696 (total_questions : ℕ) (h : total_questions = 40)
    (correct_answers : ℕ) (h1 : correct_answers = 80 * 10 / 100 + 70 * 30 / 100) :
    (correct_answers * 100 : ℝ) / total_questions = 72.5 := by 
  have h2 : correct_answers = 29 := by
    norm_num [h1]
  have h3 : total_questions = 40 := h
  rw [h2, h3]
  norm_num