import Mathlib

theorem algebra_18896 {total_books mystery_books math_books science_books : ℕ} 
    (htotal : total_books = 24) (hmystery : mystery_books = 8) 
    (hmath : math_books = 10) (hscience : science_books = 6) :
    (math_books - 2) / (total_books - 6) = (4 / 9 : ℝ) := by
  rw [htotal, hmath]
  norm_num