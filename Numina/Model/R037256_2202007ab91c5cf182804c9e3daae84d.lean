import Mathlib

theorem algebra_213394 {a : ℝ} (ha : a ≠ 0) (h : a / 2 - 2 / a = 3) :
    (a ^ 12 + 4096) / (64 * a ^ 6) = 1298 := by
  have h1 : a ^ 2 - 6 * a - 4 = 0 := by 
    field_simp [ha] at h
    linarith
  have h2 : a ^ 2 = 6 * a + 4 := by 
    linarith [h1]
  have h3 : a ^ 3 = 40 * a + 24 := by 
    calc
      a ^ 3 = a * (a ^ 2) := by ring
      _ = a * (6 * a + 4) := by rw [h2]
      _ = 6 * a ^ 2 + 4 * a := by ring
      _ = 6 * (6 * a + 4) + 4 * a := by rw [h2]
      _ = 40 * a + 24 := by ring
  have h6 : a ^ 6 = 11520 * a + 6976 := by
    calc
      a ^ 6 = (a ^ 3) ^ 2 := by ring
      _ = (40 * a + 24) ^ 2 := by rw [h3]
      _ = 1600 * a ^ 2 + 1920 * a + 576 := by ring
      _ = 1600 * (6 * a + 4) + 1920 * a + 576 := by rw [h2]
      _ = 11520 * a + 6976 := by ring
  have h12 : a ^ 12 = (11520 * a + 6976) ^ 2 := by
    calc
      a ^ 12 = (a ^ 6) ^ 2 := by ring
      _ = (11520 * a + 6976) ^ 2 := by rw [h6]
  field_simp [show a ≠ 0 by exact ha, show a ^ 6 ≠ 0 by
    intro h'
    have : a = 0 := by
      have h7 : a ^ 6 = 0 := by linarith
      have h8 : a ^ 2 = 0 := by
        nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4), sq_nonneg (a ^ 5), sq_nonneg (a ^ 6)]
      have h9 : a = 0 := by
        nlinarith [h2, h8]
      exact h9
    contradiction
  ]
  <;> nlinarith [sq_nonneg (a ^ 2 - 6 * a - 4), sq_nonneg (a ^ 3 - 40 * a - 24), sq_nonneg (a ^ 6 - 11520 * a - 6976), 
    sq_nonneg (a + 2), sq_nonneg (a - 3 - Real.sqrt 13), sq_nonneg (a - 3 + Real.sqrt 13), 
    Real.sqrt_nonneg 13, Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num)]