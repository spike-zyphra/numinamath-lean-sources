import Mathlib

theorem algebra_12912 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 4 130}.encard = 64 := by
  have h1 : {x : ℕ | Even x ∧ x ∈ Finset.Icc 4 130} = Finset.filter (fun x => Even x) (Finset.Icc 4 130) := by
    ext x
    simp [Finset.mem_Icc]
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide