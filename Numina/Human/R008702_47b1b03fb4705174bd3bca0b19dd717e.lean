import Mathlib

/- The average age of 33 fifth-graders is 11. The average age of 55 of their parents is 33. What is the average age of all of these parents and fifth-graders? -/
theorem algebra_14009 (fifth_graders : Fin 33 → ℕ) (parents : Fin 55 → ℕ)
    (h0 : (∑ i, fifth_graders i : ℝ) / 33 = 11)
    (h1 : (∑ i, parents i : ℝ) / 55 = 33) :
    ((∑ i, fifth_graders i : ℝ) + (∑ i, parents i : ℝ)) / (33 + 55) = 24.75 := by
  trans (33 * 66) / 88
  . congr 1
    . linarith
    . norm_num
  . norm_num