import Mathlib

theorem algebra_268237 (a : Fin 7 → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 100)
    (h1 : (a 0 + a 1 + a 2 + a 3 + a 4) / 5 = (a 0 + a 1 + a 2) / 3 - 1)
    (h2 : (a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6) / 7 = (a 0 + a 1 + a 2 + a 3 + a 4) / 5 - 3)
    (h3 : (a 3 + a 4 + a 5 + a 6) / 4 = 84) :
    (a 0 + a 1 + a 2) / 3 = 91 := by
  have h3' : a 3 + a 4 + a 5 + a 6 = 336 := by
    linarith

  have eq1 : 3 * (a 3 + a 4) = 2 * (a 0 + a 1 + a 2) - 15 := by 
    linarith
  
  have eq2 : 5 * (a 5 + a 6) = 2 * (a 0 + a 1 + a 2 + a 3 + a 4) - 105 := by 
    linarith
  
  have h4 : a 3 + a 4 = 177 := by 
    linarith [h3']

  have h5 : a 0 + a 1 + a 2 = 273 := by
    linarith [h4, eq1]

  linarith