import Mathlib

theorem number_theory_22911 :
    Set.ncard {m : ℕ | 0 < m ∧ m < 100 ∧ (Nat.gcd m 100) < 10} = 88 := by 
  have h1 : {m : ℕ | 0 < m ∧ m < 100 ∧ (Nat.gcd m 100) < 10} = Finset.filter (fun m => 0 < m ∧ m < 100 ∧ (Nat.gcd m 100) < 10) (Finset.Icc 0 100) := by
    ext m
    simp
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide