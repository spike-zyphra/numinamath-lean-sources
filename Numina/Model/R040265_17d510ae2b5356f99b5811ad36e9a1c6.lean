import Mathlib

theorem algebra_108634 {G : Type*} [CommGroup G] [Fintype G]
    (hG : Fintype.card G = 2015) (x : G) (hx : x^2 = 1) : x = 1 := by
  have h2 : x ^ 2 = 1 := hx
  have h3 : orderOf x ∣ 2 := by
    have h6 : x ^ 2 = 1 := h2
    exact orderOf_dvd_of_pow_eq_one h6
  have h4 : orderOf x ∣ 2015 := by 
    have h5 : orderOf x ∣ Fintype.card G := by 
      apply orderOf_dvd_card
    rw [hG] at h5 
    exact h5 
  have h5 : orderOf x ∣ 1 := by 
    exact Nat.dvd_gcd h3 h4 
  have h6 : orderOf x = 1 := by 
    have h7 : orderOf x ∣ 1 := h5 
    have h8 : orderOf x = 1 := by 
      exact Nat.dvd_one.mp h7 
    exact h8 
  have h8 : x = 1 := by
    have h9 : orderOf x = 1 := h6
    have h10 : x ^ (orderOf x) = 1 := by 
      rw [pow_orderOf_eq_one]
    rw [h9] at h10
    simp at h10 ⊢ 
    exact h10
  exact h8 
  all_goals tauto
  all_goals tauto