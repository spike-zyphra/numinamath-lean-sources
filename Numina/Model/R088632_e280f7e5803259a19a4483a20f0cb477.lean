import Mathlib

theorem number_theory_144447 :
    ∃ x : ℤ, (x - 1) ∣ (x - 3) ∧
    ∃ x : ℤ, (x + 2) ∣ (x ^ 2 + 3) := by 
  use 2
  constructor
  · -- Show that (2 - 1) divides (2 - 3)
    norm_num
  · -- Show existence of another integer x where (x + 2) divides (x ^ 2 + 3)
    use -1
    norm_num