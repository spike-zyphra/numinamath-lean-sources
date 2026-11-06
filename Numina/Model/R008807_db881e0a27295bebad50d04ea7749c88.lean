import Mathlib

theorem number_theory_4705 {n : ℤ} : n = 2101 →
    n ≡ 0 [ZMOD 11] ∧ n ≡ 1 [ZMOD 2] ∧
    n ≡ 1 [ZMOD 3] ∧ n ≡ 1 [ZMOD 5] ∧
    n ≡ 1 [ZMOD 7] := by 
  intro hn 
  rw [hn]
  constructor 
  · -- Show that 2101 ≡ 0 (mod 11)
    norm_num [Int.ModEq]
  constructor 
  · -- Show that 2101 ≡ 1 (mod 2)
    norm_num [Int.ModEq]
  constructor 
  · -- Show that 2101 ≡ 1 (mod 3)
    norm_num [Int.ModEq]
  constructor 
  · -- Show that 2101 ≡ 1 (mod 5)
    norm_num [Int.ModEq]
  · -- Show that 2101 ≡ 1 (mod 7)
    norm_num [Int.ModEq]