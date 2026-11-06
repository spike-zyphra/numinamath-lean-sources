import Mathlib

theorem number_theory_286392 :
    ∃ m n : ℕ, m.Coprime n ∧ (Nat.card {k | k ∈ Finset.Icc 1 500 ∧ (7 ∣ k ∨ 11 ∣ k)}) * n = m * (Nat.card {k | k ∈ Finset.Icc 1 500}) := by 
  use 11, 50 
  constructor
  · -- Show that 11 and 50 are coprime 
    norm_num [Nat.Coprime]
  · -- Show the equation holds
    have h1 : Nat.card {k | k ∈ Finset.Icc 1 500 ∧ (7 ∣ k ∨ 11 ∣ k)} = 110 := by
      have h2 : {k | k ∈ Finset.Icc 1 500 ∧ (7 ∣ k ∨ 11 ∣ k)} = Finset.filter (fun k => 7 ∣ k ∨ 11 ∣ k) (Finset.Icc 1 500) := by
        ext k
        simp
      rw [h2]
      rw [Nat.card_eq_fintype_card]
      native_decide
    have h2 : Nat.card {k | k ∈ Finset.Icc 1 500} = 500 := by
      have h3 : {k | k ∈ Finset.Icc 1 500} = Finset.Icc 1 500 := by
        ext k
        simp
      rw [h3]
      rw [Nat.card_eq_fintype_card]
      native_decide
    rw [h1, h2]
    all_goals norm_num