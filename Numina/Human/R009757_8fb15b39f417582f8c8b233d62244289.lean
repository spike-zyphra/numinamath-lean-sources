import Mathlib

/- How many 3-letter sequences can be formed if the second letter must be a vowel (A, E, I, O, or U), and the third letter must be different from the first letter? -/
theorem algebra_21655 :
    Set.encard {x : Fin 3 → Fin 26 | x 2 ≠ x 0 ∧ x 1 ∈ ({0, 4, 8, 14, 20} : Finset _)} = 3250 := by
  simp [Set.encard]
  native_decide
