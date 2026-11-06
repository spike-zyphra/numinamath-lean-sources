import Mathlib
open Mathlib
lemma algebra_1163 (total_a remaining_lower_than_a : ℚ) (h1 : total_a = (80 : ℚ) / 100 * 50) (h2 : (22 + (50 - 30 - remaining_lower_than_a)) = total_a) : remaining_lower_than_a = 2 := by 
  have ht : total_a = (40 : ℚ) := by 
    linarith
  rw [ht] at h2 
  linarith