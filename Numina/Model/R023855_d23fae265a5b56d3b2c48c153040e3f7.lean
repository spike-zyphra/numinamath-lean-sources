import Mathlib

open Real

theorem algebra_99438 {a : ℕ → ℝ} (ha1 : a 1 = 3 / 2)
    (han : ∀ n > 0, a (n + 1) = (a n + 1 / a n) / 2) :
    (Nat.floor (10 ^ 22 * a 6)) % 100 = 0 := by

  have ha2 : a 2 = 13 / 12 := by 
    rw [han 1 (by norm_num), ha1]
    norm_num

  have ha3 : a 3 = 313 / 312 := by
    rw [han 2 (by norm_num), ha2]
    norm_num

  have ha4 : a 4 = 195313 / 195312 := by
    rw [han 3 (by norm_num), ha3]
    norm_num

  have ha5 : a 5 = (195313 ^ 2 + 195312 ^ 2) / (2 * 195312 * 195313) := by 
    rw [han 4 (by norm_num), ha4]
    field_simp
    <;> norm_num

  have ha6 : a 6 = ((195313^2 + 195312^2)^2 + (2 * 195312 * 195313)^2) / (2 * (195313^2 + 195312^2) * (2 * 195312 * 195313)) := by
    rw [han 5 (by norm_num), ha5]
    field_simp
    <;> norm_num
    <;> field_simp
    <;> norm_num
  
  -- Calculate Nat.floor
  have h7 : Nat.floor (10 ^ 22 * a 6) = 10000000000000000000000 := by
    rw [ha6]
    norm_num [Nat.floor_eq_iff]

  -- Calculate the modulo
  calc 
    (Nat.floor (10 ^ 22 * a 6)) % 100 = 10000000000000000000000 % 100 := by rw [h7]
    _ = 0 := by norm_num