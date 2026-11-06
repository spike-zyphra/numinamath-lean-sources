import Mathlib
open Mathlib
lemma algebra_1182 (boys : ℕ) (girls : ℕ) (initial : (↑girls : ℚ) = (40 : ℚ) / (100 : ℚ) * ((↑boys : ℚ) + (↑girls : ℚ))) (thereafter : ((↑girls : ℚ) - 2) = (30 : ℚ) / (100 : ℚ) * (((↑boys : ℚ) + 2) + ((↑girls : ℚ) - 2))) : girls = 8 := by
  have eq1 : (↑girls : ℚ) = (40 : ℚ) / (100 : ℚ) * ((↑boys : ℚ) + (↑girls : ℚ)) := initial
  have eq2 : ((↑girls : ℚ) - 2) = (30 : ℚ) / (100 : ℚ) * (((↑boys : ℚ) + 2) + ((↑girls : ℚ) - 2)) := thereafter
  have eq3 : (↑boys : ℚ) = (3 / 2 : ℚ) * (↑girls : ℚ) := by
    linarith
  have eq5 : (↑girls : ℚ) = 8 := by
    rw [show (↑boys : ℚ) = (3 / 2 : ℚ) * (↑girls : ℚ) by linarith] at eq2
    linarith
  have eq6 : (girls : ℚ) = (8 : ℚ) := by
    linarith
  exact_mod_cast eq6