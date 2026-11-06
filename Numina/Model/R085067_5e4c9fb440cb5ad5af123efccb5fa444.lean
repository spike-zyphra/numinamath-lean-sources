import Mathlib

theorem algebra_311091 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h1 : abs (b - 2) + b - 2 = 0) (h2 : abs (a - b) + a - b = 0) (h3 : a ≠ b) :
    a * b = 2 := by
  have h4 : abs (b - 2) = 2 - b := by linarith
  have h5 : 2 - b ≥ 0 := by 
    have h6 : abs (b - 2) ≥ 0 := abs_nonneg (b - 2)
    linarith [h4, h6]
  have h7 : b ≤ 2 := by linarith
  have h8 : b = 1 ∨ b = 2 := by
    omega
  rcases h8 with h9 | h10
  · -- Case b = 1
    have h11 : a < b := by
      rw [show b = 1 by linarith [h9]] at h2
      have h12 : abs (a - 1) + a - 1 = 0 := by 
        linarith
      have h13 : abs (a - 1) = 1 - a := by linarith
      have h14 : 1 - a ≥ 0 := by 
        have h15 : abs (a - 1) ≥ 0 := abs_nonneg (a - 1)
        linarith [h13, h15]
      have h16 : a ≤ 1 := by linarith
      have h17 : a = 1 := by omega
      omega
    have h18 : a = b := by 
      omega
    exfalso
    exact h3 (by omega)
  · -- Case b = 2
    have h19 : a < b := by
      rw [show b = 2 by linarith [h10]] at h2
      have h20 : abs (a - 2) + a - 2 = 0 := by
        linarith
      have h21 : abs (a - 2) = 2 - a := by linarith
      have h22 : 2 - a ≥ 0 := by
        have h23 : abs (a - 2) ≥ 0 := abs_nonneg (a - 2)
        linarith [h21, h23]
      have h24 : a ≤ 2 := by linarith
      omega
    have h26 : a = 1 := by
      omega
    have h27 : b = 2 := by linarith [h10]
    rw [h26, h27]
    norm_num