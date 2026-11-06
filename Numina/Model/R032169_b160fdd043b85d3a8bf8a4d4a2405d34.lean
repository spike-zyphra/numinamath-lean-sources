import Mathlib

theorem number_theory_12884 :
    Set.ncard {x : ℕ | x > 0 ∧ x ≤ 2020 ∧ 15 ∣ (x ^ 2 + 2 * x - 3)} = 539 := by
  have h1 : {x : ℕ | x > 0 ∧ x ≤ 2020 ∧ 15 ∣ (x ^ 2 + 2 * x - 3)} = Finset.filter (fun x => x > 0 ∧ x ≤ 2020 ∧ 15 ∣ (x ^ 2 + 2 * x - 3)) (Finset.Icc 1 2020) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide