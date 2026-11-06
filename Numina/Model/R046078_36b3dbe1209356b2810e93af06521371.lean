import Mathlib

theorem algebra_7378 {x : ℝ} (hx : x ≠ 2) (h : 8 / (x ^ 2 - 4) = 2 / (x - 2) + 1) :
    x = -4 := by
  have h1 : x - 2 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h2 : x ^ 2 - 4 = (x - 2) * (x + 2) := by
    ring
  have h3 : x + 2 ≠ 0 := by
    by_contra h4
    have h4' : x = -2 := by linarith
    rw [h4'] at h
    norm_num at h
  have eq1 : 8 / (x ^ 2 - 4) = 2 / (x - 2) + 1 := h
  have eq2 : 8 = 2 * (x + 2) + (x ^ 2 - 4) := by
    have h4 : x - 2 ≠ 0 := h1
    have h5 : x + 2 ≠ 0 := h3
    have h6 : x ^ 2 - 4 ≠ 0 := by
      intro h7
      have : (x + 2) * (x - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 this) with h7 h8
      · -- x + 2 = 0
        exfalso
        apply h3
        linarith
      · -- x - 2 = 0
        exfalso
        apply h1
        linarith
    have eq1' : 8 / (x ^ 2 - 4) = 2 / (x - 2) + 1 := h
    field_simp [(show x ^ 2 - 4 ≠ 0 by assumption), (show x - 2 ≠ 0 by assumption), (show x + 2 ≠ 0 by assumption)] at eq1' ⊢
    <;> nlinarith [sq_pos_of_ne_zero (show (x - 2) ≠ 0 by assumption), sq_pos_of_ne_zero (show (x + 2) ≠ 0 by assumption)]
  have eq3 : x ^ 2 + 2 * x - 8 = 0 := by
    nlinarith [eq2]
  have eq4 : (x + 4) * (x - 2) = 0 := by
    nlinarith [eq3]
  cases' (mul_eq_zero.1 eq4) with h5 h6
  · -- x + 4 = 0, hence x = -4.
    linarith
  · -- x - 2 = 0, hence x = 2, which is in contradiction with hx : x ≠ 2.
    exfalso
    apply hx
    linarith