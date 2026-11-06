import Mathlib
open Mathlib
/--
Some boys and girls are having a car wash to raise money for a class trip to China. Initially $40\%$ of the group are girls. Shortly thereafter two girls leave and two boys arrive, and then $30\%$ of the group are girls. How many girls were initially in the group?
-/
lemma algebra_1182 (boys : ℕ) (girls : ℕ) (initial : (↑girls : ℚ) = (40 : ℚ) / (100 : ℚ) * ((↑boys : ℚ) + (↑girls : ℚ))) (thereafter : ((↑girls : ℚ) - 2) = (30 : ℚ) / (100 : ℚ) * (((↑boys : ℚ) + 2) + ((↑girls : ℚ) - 2))) : girls = 8 := by
  qify at *
  linarith