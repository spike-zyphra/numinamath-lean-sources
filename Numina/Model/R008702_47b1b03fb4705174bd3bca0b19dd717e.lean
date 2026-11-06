import Mathlib

theorem algebra_14009 (fifth_graders : Fin 33 → ℕ) (parents : Fin 55 → ℕ)
    (h0 : (∑ i, fifth_graders i : ℝ) / 33 = 11)
    (h1 : (∑ i, parents i : ℝ) / 55 = 33) :
    ((∑ i, fifth_graders i : ℝ) + (∑ i, parents i : ℝ)) / (33 + 55) = 24.75 := by
  have h2 : (∑ i, fifth_graders i : ℝ) = 363 := by
    linarith
  have h3 : (∑ i, parents i : ℝ) = 1815 := by
    linarith
  rw [h2, h3]
  norm_num