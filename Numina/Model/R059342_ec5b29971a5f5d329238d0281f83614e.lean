import Mathlib

theorem number_theory_240558 : {x : ℕ | x ∈ Finset.Icc (2^10) (2^18) ∧ 2^9 ∣ x}.ncard = 511 := by

  have : {x : ℕ | x ∈ Finset.Icc (2^10) (2^18) ∧ 2^9 ∣ x} = Finset.filter (λx =>
      2^9 ∣ x) (Finset.Icc (2^10) (2^18)) := by
    ext
    simp
    <;> tauto

  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide