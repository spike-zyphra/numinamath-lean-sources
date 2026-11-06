import Mathlib

theorem number_theory_242653 : {i | i ∈ (Nat.digits 10 (987654321 * 9)) ∧ i = 9}.encard = 1 := by
  have h1 : 987654321 * 9 = 8888888889 := by norm_num
  have h2 : Nat.digits 10 (8888888889 : ℕ) = [9,8,8,8,8,8,8,8,8,8] := by
    norm_num
  have h3 : (Nat.digits 10 (987654321 * 9)) = [9,8,8,8,8,8,8,8,8,8] := by
    rw [h1]
    all_goals rw [h2]
  have h4 : {i | i ∈ (Nat.digits 10 (987654321 * 9)) ∧ i = 9} = {9} := by
    ext x
    simp [h3]
    <;> omega
  rw [h4]
  simp [Set.encard]
  all_goals try tauto