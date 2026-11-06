import Mathlib

theorem algebra_609445 (x y z : ℤ) (h₁: (x + y: ℝ) / 2 + z = 42) 
    (h₂ : (y + z: ℝ) / 2 + x = 13) (h₃ : (x + z: ℝ) / 2 + y = 37) :
    x = -20 ∧ y = 28 ∧ z = 38 := by

  have eq1 : (x + y + 2 * z : ℝ) = 84 := by
    linarith [h₁]

  have eq1' : x + y + 2 * z = 84 := by 
    exact_mod_cast eq1

  have eq2 : (y + z + 2 * x : ℝ) = 26 := by
    linarith [h₂]

  have eq2' : y + z + 2 * x = 26 := by 
    exact_mod_cast eq2

  have eq3 : (x + z + 2 * y : ℝ) = 74 := by 
    linarith [h₃]

  have eq3' : x + z + 2 * y = 74 := by
    exact_mod_cast eq3

  have eq4 : x + y + z = 46 := by
    linarith [eq1', eq2', eq3']

  have hz : z = 38 := by
    linarith [eq1', eq4]

  have hx : x = -20 := by
    linarith [eq2', eq4]

  have hy : y = 28 := by 
    linarith [eq3', eq4]

  exact ⟨hx, hy, hz⟩