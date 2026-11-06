import Mathlib

theorem number_theory_15735 : Set.ncard {n : ℕ | n ∈ Set.Icc 100 999 ∧ 11 ∣ n ∧ 5 ∣ n} = 17 := by
  have h1 : {n : ℕ | n ∈ Set.Icc 100 999 ∧ 11 ∣ n ∧ 5 ∣ n} = Finset.filter (λ n => 11 ∣ n ∧ 5 ∣ n) (Finset.Icc 100 999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide