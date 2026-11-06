import Mathlib

theorem algebra_177297 {x : ℝ} (hx : x > 0) (h : x ^ 2 + 1 / x ^ 2 = 7) :
    x ^ 5 + 1 / x ^ 5 = 123 := by
  have h1 : x + 1 / x = 3 := by
    have h2 : (x + 1 / x) ^ 2 = 9 := by
      have h3 : (x + 1 / x) ^ 2 = x^2 + 1/x^2 + 2 := by
        field_simp
        <;> ring
      rw [h3, h]
      all_goals norm_num
    have h4 : x + 1 / x > 0 := by
      have h5 : x + 1 / x > 0 := by
        apply add_pos
        · linarith
        · positivity
      linarith
    have h6 : x + 1 / x = 3 := by
      have h7 : (x + 1 / x) ^ 2 - 9 = 0 := by linarith [h2]
      have h8 : (x + 1 / x - 3) * (x + 1 / x + 3) = 0 := by
        ring_nf at h7 ⊢
        linarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · linarith
      · linarith [show x + 1 / x ≤ 0 from by linarith, h4]
    exact h6
  have h3 : x^3 + 1 / x^3 = 18 := by
    have h4 : x^3 + 1 / x^3 = (x + 1 / x)^3 - 3 * (x + 1 / x) := by
      field_simp
      <;> ring
    rw [h4, h1]
    all_goals norm_num
  have h4 : x^4 + 1 / x^4 = 47 := by
    have h5 : x^4 + 1 / x^4 = (x^2 + 1 / x^2)^2 - 2 := by
      field_simp
      <;> ring
    rw [h5, h]
    all_goals norm_num
  have h5 : x ^ 5 + 1 / x ^ 5 = (x + 1 / x) * (x^4 + 1 / x^4) - (x^3 + 1 / x^3) := by
    field_simp
    <;> ring
  rw [h5, h1, h4, h3]
  all_goals norm_num