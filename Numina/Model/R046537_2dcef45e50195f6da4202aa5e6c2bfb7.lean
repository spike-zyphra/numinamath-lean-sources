import Mathlib

theorem algebra_164212 {a b c p : ℝ}
    (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a)
    (hanz : a ≠ 0) (hbnz : b ≠ 0) (hcnz : c ≠ 0)
    (h1 : a + 1 / b = p) (h2 : b + 1 / c = p) (h3 : c + 1 / a = p) :
    p = 1 ∨ p = - 1 := by 
  have eq1 : a * b + 1 = p * b := by
    have h1' : a + 1 / b = p := h1
    field_simp [hbnz] at h1'
    linarith

  have eq2 : b * c + 1 = p * c := by
    have h2' : b + 1 / c = p := h2
    field_simp [hcnz] at h2'
    linarith

  have eq3 : c * a + 1 = p * a := by
    have h3' : c + 1 / a = p := h3
    field_simp [hanz] at h3'
    linarith

  have eq4 : (p - 1) * (p + 1) = 0 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha), sq_pos_of_ne_zero (sub_ne_zero_of_ne hb), sq_pos_of_ne_zero (sub_ne_zero_of_ne hc), sq_pos_of_ne_zero hanz, sq_pos_of_ne_zero hbnz, sq_pos_of_ne_zero hcnz]
  
  have eq5 : p - 1 = 0 ∨ p + 1 = 0 := by
    apply mul_eq_zero.mp
    linarith

  cases eq5 with
  | inl h =>
    left
    linarith
  | inr h =>
    right
    linarith