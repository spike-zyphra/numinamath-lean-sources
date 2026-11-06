import Mathlib

theorem number_theory_123361 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (3 ^ n + n ^ 3)} = 288 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (3 ^ n + n ^ 3)} = Finset.filter (fun (n : ℕ) => 7 ∣ (3 ^ n + n ^ 3) ∧ 1 ≤ n ∧ n ≤ 2015) (Finset.Icc 0 2015) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide