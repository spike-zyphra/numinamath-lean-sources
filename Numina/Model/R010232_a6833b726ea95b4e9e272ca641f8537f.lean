import Mathlib

theorem number_theory_17067 : { n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd 15 n = 3}.ncard = 27 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd 15 n = 3} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd 15 n = 3) (Finset.Icc 0 100) := by
    ext n
    simp 
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide