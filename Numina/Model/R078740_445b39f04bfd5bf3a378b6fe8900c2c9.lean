import Mathlib

theorem number_theory_289226 : {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (3^n + n^3)}.encard = 288 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2015 ∧ 7 ∣ (3^n + n^3)} = Finset.filter (fun n => 7 ∣ (3^n + n^3) ) (Finset.Icc (1 : ℕ) 2015) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide