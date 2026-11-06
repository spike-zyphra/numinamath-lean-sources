import Mathlib

theorem number_theory_8922 :
    Set.ncard {n : ℕ | 0 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (6 ^ n + 8 ^ n)} = 1008 := by
  have h1 : {n : ℕ | 0 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (6 ^ n + 8 ^ n)} = Finset.filter (λn => 0 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (6 ^ n + 8 ^ n)) (Finset.Icc 0 2015) := by
    ext n 
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide