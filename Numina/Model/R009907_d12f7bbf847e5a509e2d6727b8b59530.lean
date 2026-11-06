import Mathlib

theorem number_theory_63976 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x} = 20 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x} = Finset.filter (fun x => 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x) (Finset.Icc 1 100) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide