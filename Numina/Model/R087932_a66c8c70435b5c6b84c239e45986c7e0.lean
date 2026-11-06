import Mathlib

theorem number_theory_4 :
    Set.ncard {A : ℕ | A ∈ Finset.Icc 10 99 ∧ A^2 ≡ 1 [MOD 15]} = 24 := by
  have h1 : {A : ℕ | A ∈ Finset.Icc 10 99 ∧ A^2 ≡ 1 [MOD 15]} = Finset.filter (fun A => A^2 ≡ 1 [MOD 15]) (Finset.Icc 10 99) := by
    ext A
    simp [Finset.mem_filter]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide