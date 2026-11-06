import Mathlib

theorem number_theory_90698 : {i | ¬(65 ∣ Nat.choose 65 i)}.encard = 16 := by
  have h : {i | ¬(65 ∣ Nat.choose 65 i)} = Finset.filter (fun i => ¬(65 ∣ Nat.choose 65 i)) (Finset.Iic 65) := by
    ext n
    simp
    intro h1
    by_contra h
    push_neg at h
    have h2 : n > 65 := h
    have h3 : Nat.choose 65 n = 0 := by
      apply Nat.choose_eq_zero_of_lt
      all_goals omega
    omega
  rw [h]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide