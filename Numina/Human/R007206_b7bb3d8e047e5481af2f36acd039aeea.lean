import Mathlib

/- A bookcase has 3 shelves with a total of 24 books. The top shelf has 8 mystery books. The middle shelf has 10 math books. The bottom shelf has 6 science books. Two books are now taken off each shelf. What fraction of the books remaining on the three shelves are math books? Express your answer as a common fraction. -/
theorem algebra_18896 {total_books mystery_books math_books science_books : ℕ} 
    (htotal : total_books = 24) (hmystery : mystery_books = 8) 
    (hmath : math_books = 10) (hscience : science_books = 6) :
    (math_books - 2) / (total_books - 6) = (4 / 9 : ℝ) := by 
  subst_vars
  norm_num