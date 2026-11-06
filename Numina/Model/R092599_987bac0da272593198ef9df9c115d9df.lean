import Mathlib

theorem algebra_185960 (α : ℝ) :
    3 * (Real.sin (α - 270 * Real.pi / 180))^2 -
    (Real.cos (α + 270 * Real.pi / 180))^2 =
    4 * Real.cos (30 * Real.pi / 180 + α) * Real.cos (30 * Real.pi / 180 - α) := by 
  have h1 : Real.sin (α - 270 * Real.pi / 180) = Real.cos α := by 
    have h5 : Real.sin (α - 270 * Real.pi / 180) = Real.sin (α + Real.pi / 2) := by 
      have h0 : α - 270 * Real.pi / 180 = α + Real.pi / 2 - 2 * Real.pi := by
        ring_nf 
      rw [h0]
      have h1 : Real.sin (α + Real.pi / 2 - 2 * Real.pi) = Real.sin (α + Real.pi / 2) := by
        rw [show α + Real.pi / 2 - 2 * Real.pi = (α + Real.pi / 2) - 2 * Real.pi by ring]
        rw [Real.sin_sub_two_pi]
      exact h1
    rw [h5]
    rw [Real.sin_add]
    simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
    <;> ring_nf <;> simp [Real.sin_sq]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> nlinarith [Real.sin_sq_add_cos_sq α]
  have h2 : Real.cos (α + 270 * Real.pi / 180) = Real.sin α := by 
    have h6 : Real.cos (α + 270 * Real.pi / 180) = Real.cos (α - Real.pi / 2) := by 
      have h7 : α + 270 * Real.pi / 180 = α - Real.pi / 2 + 2 * Real.pi := by 
        ring_nf 
      rw [h7]
      have h8 : Real.cos (α - Real.pi / 2 + 2 * Real.pi) = Real.cos (α - Real.pi / 2) := by 
        rw [show α - Real.pi / 2 + 2 * Real.pi = (α - Real.pi / 2) + 2 * Real.pi by ring]
        rw [Real.cos_add_two_pi]
      exact h8
    rw [h6]
    have h9 : Real.cos (α - Real.pi / 2) = Real.sin α := by 
      rw [Real.cos_sub]
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
      <;> ring_nf <;> simp [Real.sin_sq]
      <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
      <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
      <;> nlinarith [Real.sin_sq_add_cos_sq α]
    exact h9
  have h3 : Real.cos (30 * Real.pi / 180 + α) = Real.cos (30 * Real.pi / 180) * Real.cos α - Real.sin (30 * Real.pi / 180) * Real.sin α := by 
    rw [Real.cos_add]
  have h4 : Real.cos (30 * Real.pi / 180 - α) = Real.cos (30 * Real.pi / 180) * Real.cos α + Real.sin (30 * Real.pi / 180) * Real.sin α := by 
    rw [Real.cos_sub]
  rw [h1, h2, h3, h4]
  have h7 : Real.cos (30 * Real.pi / 180) = Real.sqrt 3 / 2 := by 
    have : 30 * Real.pi / 180 = Real.pi / 6 := by 
      ring_nf 
    rw [this]
    exact Real.cos_pi_div_six
  have h8 : Real.sin (30 * Real.pi / 180) = 1 / 2 := by 
    have : 30 * Real.pi / 180 = Real.pi / 6 := by 
      ring_nf 
    rw [this]
    exact Real.sin_pi_div_six
  rw [h7, h8]
  all_goals nlinarith [Real.sin_sq_add_cos_sq α, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]