import Mathlib

theorem algebra_19412 {b c : ℝ}(hc : c ≠ 0)
  (hroots : ∃ x y, x ≠ y ∧
  x^2 + b * x + c = 0 ∧ y^2 + b * y + c = 0 ∧
  |x - y| = |b - 2*c|): c = b - 1 := by
  rcases hroots with ⟨x,y,hxy⟩
  have eqx: 1 * (x*x) + b*x + c = 0 := by
    linarith [hxy.right.left]
  have eqy: 1 * (y*y) + b*y + c = 0 := by
    linarith [hxy.right.right.left]
  have h1 : (x - y) * (x + y + b) = 0 := by
    nlinarith [eqx, eqy]
  have h2 : x + y + b = 0 := by
    apply (mul_right_inj' (show x - y ≠ 0 by 
      intro h'
      apply hxy.left
      linarith)).mp 
    linarith
  have h3 : x + y = -b := by linarith
  have h4 : (x - y)^2 = b^2 - 4 * c := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by 
      intro h'
      apply hxy.left
      linarith), h3, eqx, eqy]
  have h5 : (x - y)^2 = (b - 2 * c) ^ 2 := by
    have h6 : |x - y| = |b - 2 * c| := by 
      simpa using hxy.right.right.right
    have h7 : (x - y) ^ 2 = (b - 2 * c) ^ 2 := by
      calc
        (x - y) ^ 2 = (abs (x - y)) ^ 2 := by rw [sq_abs]
        _ = (abs (b - 2 * c)) ^ 2 := by rw [h6]
        _ = (b - 2 * c) ^ 2 := by rw [sq_abs]
    linarith
  rw [h5] at h4
  have h8 : c * (c - b + 1) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- h9: c = 0
    exfalso
    exact hc (by linarith)
  · -- h10: c - b + 1 = 0
    linarith