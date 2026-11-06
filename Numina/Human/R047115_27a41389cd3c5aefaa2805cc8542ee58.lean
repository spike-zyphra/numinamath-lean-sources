import Mathlib

theorem number_theory_324870 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd (n^2 + 4) (n + 3) > 1} = 7 := by 
  have : {n : ℕ | 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd (n^2 + 4) (n + 3) > 1} = Finset.filter (λ n => 1 ≤ n ∧ n ≤ 100 ∧ Nat.gcd (n^2 + 4) (n + 3) > 1) (Finset.range 101) := by
    ext n
    simp
    omega
  rw [this]
  rw [Set.ncard_coe_Finset]
  rfl