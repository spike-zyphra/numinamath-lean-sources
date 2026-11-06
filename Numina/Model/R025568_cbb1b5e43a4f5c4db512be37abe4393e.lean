import Mathlib

theorem algebra_153218 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (d t : ℝ) (ht : t > 0) (hd : d > 0) (h : d / (2 * a) = t / (2 * b)) :
    (d / (2 * a) + t / (2 * b)) < (d / (2 * b) + t / (2 * a)) := by
  have h1 : d * b = t * a := by
    field_simp [show (2 * a : ℝ) ≠ 0 by positivity, show (2 * b : ℝ) ≠ 0 by positivity] at h ⊢
    nlinarith
  have h3 : (d - t) * (1 / (2 * a) - 1 / (2 * b)) < 0 := by
    have h4 : (d - t) * (1 / (2 * a) - 1 / (2 * b)) = - (t * (a - b) ^ 2) / (2 * a * b ^ 2) := by
      have h5 : d = (t * a ) / b := by
        have h6 : d * b = t * a := h1
        field_simp [show (b : ℝ) ≠ 0 by linarith] at h6 ⊢
        nlinarith
      rw [h5]
      field_simp [show (a : ℝ) ≠ 0 by linarith, show (b : ℝ) ≠ 0 by linarith]
      <;> ring_nf
      <;> field_simp [show (a : ℝ) ≠ 0 by linarith, show (b : ℝ) ≠ 0 by linarith]
      <;> ring_nf
      <;> nlinarith
    rw [h4]
    have h5 : t * (a - b) ^ 2 > 0 := by
      have h6 : (a - b) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        intro h'
        apply hab
        linarith
      nlinarith
      all_goals nlinarith
    have h7 : - (t * (a - b) ^ 2) / (2 * a * b ^ 2) < 0 := by
      apply div_neg_of_neg_of_pos
      · -- Show negative numerator
        nlinarith
      · -- Show positive denominator
        positivity
    linarith
  have h4 : (d - t) * (1 / (2 * a) - 1 / (2 * b)) = (d / (2 * a) + t / (2 * b)) - (d / (2 * b) + t / (2 * a)) := by
    field_simp [show (a : ℝ) ≠ 0 by linarith, show (b : ℝ) ≠ 0 by linarith]
    <;> ring_nf
    <;> field_simp [show (a : ℝ) ≠ 0 by linarith, show (b : ℝ) ≠ 0 by linarith]
    <;> ring_nf
    <;> nlinarith
  have h5 : (d / (2 * a) + t / (2 * b)) - (d / (2 * b) + t / (2 * a)) < 0 := by
    linarith [h3, h4]
  linarith