import Mathlib

theorem algebra_216 {A B C : ℤ} (h₀ : A > 0) (h₁ : B > 0) (h₂ : C > 0) (h₃ : ∀ y, 6 * y ^ 2 - y - 51 = (3 * A * y + B) * (y - C)) : (A * C) ^ 2 - B = 19 := by
  have eq1 := h₃ 0
  have eq2 := h₃ 1
  have eq3 := h₃ 2
  have eq4 := h₃ 3
  have eq5 := h₃ 4
  ring_nf at eq1 eq2 eq3 eq4 eq5
  have h4 : C = 3 := by
    have eq6 : (9 * A + B) * (3 - C) = 0 := by 
      linarith 
    cases (mul_eq_zero.mp eq6) with
    | inl h6 =>
      omega -- contradiction h6 with hypothesis
    | inr h7 =>
      omega -- solve from (3 - C = 0) that (C = 3)
  have hb : B = 17 := by 
    rw [h4] at eq1
    nlinarith
  have ha : A = 2 := by 
    rw [hb, h4] at eq2
    nlinarith
  calc
    (A * C) ^ 2 - B = (2 * 3) ^ 2 - 17 := by rw [ha, hb, h4]
    _ = 6 ^ 2 - 17 := by norm_num
    _ = 36 - 17 := by norm_num
    _ = 19 := by norm_num