import Mathlib

theorem number_theory_60555 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Odd (Nat.divisors n).card} = 10 := by 
  have h : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Odd (Nat.divisors n).card} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 100 ∧ Odd (Nat.divisors n).card) (Finset.Icc (0 : ℕ) 100) := by
    ext n
    simp 
    <;> omega 
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide