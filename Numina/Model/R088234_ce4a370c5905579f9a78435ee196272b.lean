import Mathlib

theorem number_theory_241458 :
    Set.ncard {x : ℤ | -1000 < x ∧ x < 1000 ∧ 3 ∣ x} >
    Set.ncard {y : ℤ | -444 < y ∧ y < 444 ∧ ¬4 ∣ y} := by

  have h1 : {x : ℤ | -1000 < x ∧ x < 1000 ∧ 3 ∣ x} = Finset.filter (λ x => 3 ∣ x) (Finset.Icc (-999) 999) := by
    ext x
    simp
    omega

  have h2 : {y : ℤ | -444 < y ∧ y < 444 ∧ ¬4 ∣ y} = Finset.filter (λ y => ¬4 ∣ y) (Finset.Icc (-443) 443) := by
    ext y
    simp
    omega

  rw [h1, h2]

  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]

  native_decide