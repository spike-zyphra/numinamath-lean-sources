import Mathlib

def is_chunky (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ n % d = 0

theorem number_theory_241661 :
    Set.ncard {n | 13 ≤ n ∧ n < 113 ∧ is_chunky n} = 14 := by
  have : {n | 13 ≤ n ∧ n < 113 ∧ is_chunky n} = Finset.filter (fun n => 13 ≤ n ∧ n < 113 ∧ (∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ n % d = 0)) (Finset.Icc 0 112) := by
    ext n
    simp [is_chunky]
    <;> omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide