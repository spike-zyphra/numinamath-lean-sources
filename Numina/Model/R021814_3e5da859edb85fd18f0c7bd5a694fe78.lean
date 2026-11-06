import Mathlib

theorem number_theory_149309 :
    Set.ncard {n : ℕ | n ≤ 100 ∧ n ≥ 10 ∧ n % (Nat.digits 10 n).sum = 0} = 24 := by
  have h1 : {n : ℕ | n ≤ 100 ∧ n ≥ 10 ∧ n % (Nat.digits 10 n).sum = 0} = Finset.filter (λ n => n ≥ 10 ∧ n % (Nat.digits 10 n).sum = 0) (Finset.Iic 100) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide