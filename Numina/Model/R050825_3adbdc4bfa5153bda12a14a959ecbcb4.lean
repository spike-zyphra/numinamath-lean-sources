import Mathlib

theorem number_theory_286356 : {n : ℕ | n ∈ Finset.Icc 208 2008 ∧ n % 10 = 1}.ncard = 180 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 208 2008 ∧ n % 10 = 1} = Finset.filter (λ n => n % 10 = 1) (Finset.Icc 208 2008) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide