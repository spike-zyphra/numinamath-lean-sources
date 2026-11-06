import Mathlib

theorem algebra_3343 {x : ℝ} (hx : abs x > 1) :
    ((x^2 - 1) / (x^3 - 1) - (x^2 - 1) / (x^3 + 1)) * ((x^2 + 1)^2 - x^2) = 2 := by
  have h1 : x ≠ 1 := by
    by_contra h
    rw [h] at hx
    norm_num [abs_of_pos] at hx
  have h2 : x ≠ -1 := by
    by_contra h
    rw [h] at hx
    norm_num [abs_of_nonneg] at hx

  have h3 : x^3 - 1 ≠ 0 := by
    by_contra h
    have h4 : x = 1 := by
      have h5 : x^3 = 1 := by linarith
      have h7 : (x - 1) * (x^2 + x + 1) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · linarith
      · -- x^2 + x + 1 = 0 
        have h10 : x^2 + x + 1 > 0 := by 
          nlinarith [sq_nonneg (x + 1 / 2)]
        nlinarith
    exfalso
    apply h1
    linarith

  have h4 : x^3 + 1 ≠ 0 := by
    by_contra h
    have h5 : x = -1 := by
      have h6 : x^3 = -1 := by linarith
      have h7 : (x + 1) * (x^2 - x + 1) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- x + 1 = 0 
        linarith
      · -- x^2 - x + 1 = 0 
        have h10 : x^2 - x + 1 > 0 := by 
          nlinarith [sq_nonneg (x - 1 / 2)]
        nlinarith
    exfalso
    apply h2
    linarith
  have eq1 : ((x^2 - 1) / (x^3 - 1) - (x^2 - 1) / (x^3 + 1)) = 2 * (x^2 - 1) / ((x^3 - 1) * (x^3 + 1)) := by 
    field_simp [(show x^3 - 1 ≠ 0 by assumption), (show x^3 + 1 ≠ 0 by assumption)]
    <;> ring
  have eq2 : ((x^2 + 1)^2 - x^2) = x^4 + x^2 + 1 := by 
    ring
  rw [eq1, eq2]
  field_simp [(show x^3 - 1 ≠ 0 by assumption), (show x^3 + 1 ≠ 0 by assumption)]
  <;> nlinarith