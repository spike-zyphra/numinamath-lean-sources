import Mathlib

theorem inequalities_34372 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    Real.sqrt ((a + b * c) * (b + c * a) / (c + a * b)) +
    Real.sqrt ((b + c * a) * (c + a * b) / (a + b * c)) +
    Real.sqrt ((c + a * b) * (a + b * c) / (b + c * a)) = 2 := by
  have h1 : c = 1 - a - b := by linarith
  have h2 : 0 < c := by linarith
  have h3 : (a + b * c) * (b + c * a) / (c + a * b) = (a + b) ^ 2 := by
    rw [show c = 1 - a - b by linarith]
    have : 0 < (1 - a - b) := by linarith
    field_simp [(show 0 < a by linarith), (show 0 < b by linarith), (show 0 < (1 - a - b) by linarith)]
    <;> ring_nf <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos (show 0 < 1 - a - b by linarith), h, mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by linarith), mul_pos hb (show 0 < 1 - a - b by linarith)]
    <;> nlinarith
  -- First term
  have h4 : Real.sqrt ((a + b * c) * (b + c * a) / (c + a * b)) = a + b := by
    rw [h3]
    rw [Real.sqrt_sq]
    nlinarith
    all_goals nlinarith
  have h5 : (b + c * a) * (c + a * b) / (a + b * c) = (b + c) ^ 2 := by
    rw [show c = 1 - a - b by linarith]
    have : 0 < (1 - a - b) := by linarith
    field_simp [(show 0 < a by linarith), (show 0 < b by linarith), (show 0 < (1 - a - b) by linarith)]
    <;> ring_nf <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos (show 0 < 1 - a - b by linarith), h, mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by linarith), mul_pos hb (show 0 < 1 - a - b by linarith)]
    <;> nlinarith
  -- Second term
  have h6 : Real.sqrt ((b + c * a) * (c + a * b) / (a + b * c)) = b + c := by
    rw [h5]
    rw [Real.sqrt_sq]
    nlinarith
    all_goals nlinarith
  -- Third term
  have h7 : (c + a * b) * (a + b * c) / (b + c * a) = (c + a) ^ 2 := by
    rw [show c = 1 - a - b by linarith]
    have : 0 < (1 - a - b) := by linarith
    field_simp [(show 0 < a by linarith), (show 0 < b by linarith), (show 0 < (1 - a - b) by linarith)]
    <;> ring_nf <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos (show 0 < 1 - a - b by linarith), h, mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by linarith), mul_pos hb (show 0 < 1 - a - b by linarith)]
    <;> nlinarith
  -- Third term
  have h8 : Real.sqrt ((c + a * b) * (a + b * c) / (b + c * a)) = c + a := by
    rw [h7]
    rw [Real.sqrt_sq]
    nlinarith
    all_goals nlinarith
  rw [h4, h6, h8]
  nlinarith [h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]