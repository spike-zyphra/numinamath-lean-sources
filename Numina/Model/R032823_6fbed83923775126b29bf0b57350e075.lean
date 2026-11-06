import Mathlib

theorem algebra_80944 {x y z : ℤ} (h1 : x - y * z = 1) (h2 : x * z + y = 2) :
    (x, y, z) = (1, 0, 2) ∨ (x, y, z) = (1, 2, 0) := by
  have h3 : x = y * z + 1 := by
    linarith
  rw [h3] at h2
  have h4 : y * (z ^ 2 + 1) = 2 - z := by
    nlinarith
  have h5 : z ≤ 2 := by
    by_contra h
    push_neg at h
    have h8 : z ≥ 3 := by nlinarith
    have h9 : z ^ 2 + 1 ≥ 10 := by
      nlinarith
    have h10 : y < 0 := by
      nlinarith
    have h11 : y * (z ^ 2 + 1) = 2 - z := h4
    nlinarith [sq_nonneg (y + 1), sq_nonneg (z - 2)]
  have h6 : z ≥ -2 := by
    by_contra h
    push_neg at h
    have h7 : z ≤ -3 := by nlinarith
    have h8 : z ^ 2 + 1 ≥ 10 := by
      nlinarith
    have h9 : y > 0 := by
      nlinarith
    nlinarith [sq_nonneg (y - 1), sq_nonneg (z + 2)]
  have h8 : z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 := by 
    omega
  rcases h8 with (h8 | h8 | h8 | h8 | h8)
  · -- z = -2
    rw [h8] at h4
    norm_num at h4
    all_goals 
      exfalso 
      all_goals 
        omega
  · -- z = -1
    rw [h8] at h4
    norm_num at h4
    all_goals 
      exfalso 
      all_goals 
        omega
  · -- z = 0
    rw [h8] at h4
    norm_num at h4 
    have hy : y = 2 := by 
      linarith
    have hx : x = 1 := by
      rw [h8, hy] at h3 
      linarith
    right
    simp [hx, hy, h8]
  · -- z = 1
    rw [h8] at h4
    norm_num at h4 
    all_goals 
      exfalso 
      all_goals 
        omega
  · -- z = 2
    rw [h8] at h4
    norm_num at h4
    have hy : y = 0 := by 
      linarith
    have hx : x = 1 := by 
      rw [h8, hy] at h3 
      linarith
    left
    simp [hx, hy, h8]