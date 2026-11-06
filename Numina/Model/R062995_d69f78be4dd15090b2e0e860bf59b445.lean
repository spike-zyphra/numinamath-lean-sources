import Mathlib

theorem number_theory_2928 : {n : ℕ | n ∈ Finset.Icc (2 ^ 2022) (2 ^ 2022 + 49) ∧ Nat.Coprime n 63}.ncard = 29 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc (2 ^ 2022) (2 ^ 2022 + 49) ∧ Nat.Coprime n 63} = 
          Finset.filter (λ n => Nat.Coprime n 63) (Finset.Icc (2 ^ 2022) (2 ^ 2022 + 49)) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide