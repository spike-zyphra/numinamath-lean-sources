import Mathlib

theorem number_theory_19538 :
    Set.ncard {n : ℕ | 0 < n ∧ n ≤ 2007 ∧ (Nat.digits 3 n).Palindrome} = 100 := by 
  have h1 : {n : ℕ | 0 < n ∧ n ≤ 2007 ∧ (Nat.digits 3 n).Palindrome} = Finset.filter (fun (n : ℕ) => 0 < n ∧ n ≤ 2007 ∧ (Nat.digits 3 n).Palindrome) (Finset.Icc 0 2007) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide