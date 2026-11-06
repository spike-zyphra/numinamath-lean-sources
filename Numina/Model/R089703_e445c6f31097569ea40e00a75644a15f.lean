import Mathlib

theorem number_theory_27457 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 2022 ∧ (402 ∣ n ^ 2 - 1 ∨ 402 ∣ n ^ 3 - 1 ∨ 402 ∣ n ^ 4 - 1)} = 31 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2022 ∧ (402 ∣ n ^ 2 - 1 ∨ 402 ∣ n ^ 3 - 1 ∨ 402 ∣ n ^ 4 - 1)} = Finset.filter (fun n : ℕ => 1 ≤ n ∧ n ≤ 2022 ∧ (402 ∣ n ^ 2 - 1 ∨ 402 ∣ n ^ 3 - 1 ∨ 402 ∣ n ^ 4 - 1)) (Finset.Icc 0 2022) := by
    ext n
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide