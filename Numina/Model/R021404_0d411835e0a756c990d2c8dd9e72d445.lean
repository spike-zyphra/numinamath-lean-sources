import Mathlib

theorem algebra_104591 (a b c d : ℚ) (h₀ : abs (a - b) ≤ 9) (h₁ : abs (c - d) ≤ 16)
    (h₂ : abs (a - b - c + d) = 25) : abs (d - c) - abs (b - a) = 7 := by
  have h3 : abs (a - b - c + d) = abs ((a - b) - (c - d)) := by
    ring_nf
  rw [h3] at h₂
  have h4 : abs ((a - b) - (c - d)) ≤ abs (a - b) + abs (c - d) := by
    apply abs_sub
  have h5 : abs (a - b) + abs (c - d) ≥ 25 := by 
    linarith [h₂, h4]
  have h6 : abs (a - b) = 9 := by 
    linarith [h₀, h₁, h5]
  have h7 : abs (c - d) = 16 := by 
    linarith [h₀, h₁, h5]
  have h8 : abs (d - c) = abs (c - d) := by
    have h9 : abs (d - c) = abs (- (c - d)) := by
      ring_nf
    rw [h9]
    have h10 : abs (- (c - d : ℚ)) = abs (c - d) := by
      rw [abs_neg]
    linarith [h10]
  have h11 : abs (b - a) = abs (a - b) := by
    have h12 : abs (b - a) = abs (- (a - b)) := by
      ring_nf
    rw [h12]
    have h13 : abs (- (a - b : ℚ)) = abs (a - b) := by
      rw [abs_neg]
    linarith [h13]
  rw [h8, h11]
  rw [h7, h6]
  all_goals norm_num