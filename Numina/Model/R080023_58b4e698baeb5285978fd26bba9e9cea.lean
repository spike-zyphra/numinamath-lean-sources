import Mathlib

theorem algebra_141882 (a b c : ℝ) (ha : a > b) (hb : b > c) (h : (a - b) * (b - c) * (c - a) = -16) :
    1 / (a - b) + 1 / (b - c) - 1 / (c - a) ≥ 5 / 4 := by

  have h1 : a - b > 0 := by linarith
  have h2 : b - c > 0 := by linarith
  have h3 : c - a < 0 := by linarith

  have h4 : (a - b) * (b - c) * (a - c) = 16 := by
    have h4 : a - c = (a - b) + (b - c) := by ring
    rw [h4] at *
    nlinarith
  
  have h5 : 1 / (a - b) + 1 / (b - c) - 1 / (c - a) = ( (b - c) * (a - c) + (a - b) * (a - c) + (a - b) * (b - c) ) / ( (a - b) * (b - c) * (a - c) ) := by
    field_simp [(show a - b ≠ 0 by nlinarith), (show b - c ≠ 0 by nlinarith), (show c - a ≠ 0 by nlinarith)]
    <;> ring

  rw [h5]

  have h7 : (b - c) * (a - c) + (a - b) * (a - c) + (a - b) * (b - c) ≥ 20 := by
    nlinarith [sq_nonneg (a - b - 2), sq_nonneg (b - c - 2), sq_nonneg (a - b - (b - c)), sq_nonneg (a - b + (b - c) - 4), 
      mul_pos (show 0 < a - b by linarith) (show 0 < b - c by linarith), 
      mul_pos (show 0 < a - b by linarith) (show 0 < a - c by nlinarith), 
      mul_pos (show 0 < b - c by linarith) (show 0 < a - c by nlinarith)
     ]

  have h9 : ( (b - c) * (a - c) + (a - b) * (a - c) + (a - b) * (b - c) ) / ( (a - b) * (b - c) * (a - c) ) ≥ 5 / 4 := by
    have h10 : (a - b) * (b - c) * (a - c) = 16 := h4
    have h11 : 0 < (a - b) * (b - c) * (a - c) := by
      nlinarith [show 0 < a - b by linarith, show 0 < b - c by linarith, show 0 < a - c by nlinarith]
    have h12 : ( (b - c) * (a - c) + (a - b) * (a - c) + (a - b) * (b - c) ) ≥ 20 := h7
    have h13 : ( (b - c) * (a - c) + (a - b) * (a - c) + (a - b) * (b - c) ) / ( (a - b) * (b - c) * (a - c) ) ≥ (20 : ℝ) / 16 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have h14 : (20 : ℝ) / 16 = 5 / 4 := by norm_num
    linarith [h13, h14]

  exact h9