import Mathlib

theorem algebra_124830 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hle : a ≤ b ∧ b ≤ c) (h : a + b + c + a * b + b * c + c * a = a * b * c + 1) : (a = 2 ∧ b = 4 ∧ c = 13) ∨ (a = 2 ∧ b = 5 ∧ c = 8) ∨ (a = 3 ∧ b = 3 ∧ c = 7) := by
  have ha2 : a ≤ 3 := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 3 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (c - 3 : ℤ)]
  have ha3 : a ≥ 2 := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (c - 1 : ℤ)]
  have h2 : a = 2 ∨ a = 3 := by
    omega
  rcases h2 with (ha2 | ha3)
  · -- Assume a = 2
    rw [show a = 2 by linarith [ha2]] at h hle
    have hb1 : b ≤ 8 := by
      nlinarith [h, hle.left, hle.right, mul_pos (show 0 < (2 : ℤ) by linarith) (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    have hb2 : b ≥ 4 := by
      nlinarith [h, hle.left, hle.right, mul_pos (show 0 < (2 : ℤ) by linarith) (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    interval_cases b <;> try { 
      omega 
    }
  · -- Assume a = 3
    rw [show a = 3 by linarith [ha3]] at h hle
    have hb1 : b ≤ 5 := by
      nlinarith [h, hle.left, hle.right, mul_pos (show 0 < (3 : ℤ) by linarith) (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    have hb2 : b ≥ 3 := by
      nlinarith [h, hle.left, hle.right, mul_pos (show 0 < (3 : ℤ) by linarith) (show 0 < b by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    interval_cases b <;> try { 
      omega 
    }