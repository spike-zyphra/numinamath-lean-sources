import Mathlib

theorem number_theory_7479 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ¬(3 ∣ n) ∧ ¬(∃ d ∈ Nat.digits 10 n, 3 ∣ d)} = 810 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ¬(3 ∣ n) ∧ ¬(∃ d ∈ Nat.digits 10 n, 3 ∣ d)} = Finset.filter (λ n => ¬(3 ∣ n) ∧ ¬(∃ d ∈ Nat.digits 10 n, 3 ∣ d)) (Finset.Icc 1000 9999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide