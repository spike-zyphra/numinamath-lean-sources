import Mathlib

def isMild (n : ℕ) := ∀ d ∈ Nat.digits 3 n, d ≠ 2

theorem number_theory_187763 :
    Set.ncard {n | 1 ≤ n ∧ n ≤ 1000 ∧ isMild n ∧ isMild (n ^ 2)} = 7 := by
  have h1 : {n | 1 ≤ n ∧ n ≤ 1000 ∧ isMild n ∧ isMild (n ^ 2)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 1000 ∧ (∀ d ∈ Nat.digits 3 n, d ≠ 2) ∧ (∀ d ∈ Nat.digits 3 (n ^ 2), d ≠ 2)) (Finset.Icc 0 1000) := by
    ext n
    simp [isMild]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide