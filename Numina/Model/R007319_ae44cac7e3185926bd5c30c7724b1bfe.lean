import Mathlib

theorem number_theory_83173 :
    Set.ncard {n : ℕ | 0 ≤ n ∧ n ≤ 720 ∧ n ^ 2 ≡ 1 [MOD 720]} = 16 := by
  have h1 : {n : ℕ | 0 ≤ n ∧ n ≤ 720 ∧ n ^ 2 ≡ 1 [MOD 720]} = Finset.filter (fun n => 0 ≤ n ∧ n ≤ 720 ∧ n^2 % 720 = 1) (Finset.Icc (0 : ℕ) 720) := by
    ext n
    simp [Nat.ModEq]
    <;> try native_decide
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide