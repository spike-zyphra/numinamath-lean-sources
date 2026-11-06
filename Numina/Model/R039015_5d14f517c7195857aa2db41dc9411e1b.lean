import Mathlib

theorem algebra_16939 (a b : List Char) (ha : a = ['M', 'A', 'T', 'T', 'C', 'O', 'U', 'N', 'T', 'S'])
    (hb : b = ['T', 'E', 'A', 'C', 'H']) :
    (a.filter fun c => c ∈ b).length / a.length = (1 / 2 : ℚ) := by
  rw [ha, hb]
  norm_num [List.length, List.filter]