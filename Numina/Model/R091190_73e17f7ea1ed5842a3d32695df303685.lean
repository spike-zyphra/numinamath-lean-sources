import Mathlib

theorem number_theory_16551 : {n | Odd n ∧ n ∈ (Nat.digits 4 (233))}.encard = 2 := by
  have h1 : Nat.digits 4 233 = [1, 2, 2, 3] := by
    norm_num [Nat.digits, Nat.digitsAux]
  have h2 : {n | Odd n ∧ n ∈ (Nat.digits 4 233)} = {1, 3} := by
    ext n
    simp [Nat.odd_iff, h1]
    <;> omega 
  rw [h2]
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num
  all_goals native_decide