import Mathlib

theorem number_theory_273871 :
    Set.ncard {n : ℕ | 10 ≤ n ∧ n < 1000 ∧ (Nat.digits 10 n).sum = 3} = 9 := by 
  have h1 : {n : ℕ | 10 ≤ n ∧ n < 1000 ∧ (Nat.digits 10 n).sum = 3} = Finset.filter (λ n => 10 ≤ n ∧ n < 1000 ∧ (Nat.digits 10 n).sum = 3) (Finset.Icc 0 999) := by
    ext n 
    simp 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide