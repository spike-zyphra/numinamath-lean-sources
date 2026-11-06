import Mathlib

theorem algebra_19765 :
    Set.ncard {x : ℕ | 0 < x ∧ 9 ∣ x ∧ x < 1000} = 111 := by 
  have h1 : {x : ℕ | 0 < x ∧ 9 ∣ x ∧ x < 1000} = Finset.filter (λ x => 0 < x ∧ 9 ∣ x ∧ x < 1000) (Finset.Icc 0 999) := by
    ext x
    simp
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide