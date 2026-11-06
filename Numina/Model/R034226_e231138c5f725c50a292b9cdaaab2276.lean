import Mathlib
set_option maxHeartbeats 800000
theorem algebra_253784 (x y z t : ℝ)
    (h₀ : x * y + z + t = 1) (h₁ : y * z + t + x = 3) (h₂ : z * t + x + y = -1)
    (h₃ : t * x + y + z = 1) :
    (x, y, z, t) = (1, 0, -1, 2) := by

  have eq1 : (x - 1) * (y - t) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq1) with h4 h5 
  · -- Case x - 1 = 0, so x = 1 
    have hx1 : x = 1 := by linarith 
    -- From hx1 : x=1, we rewrite the original equations. 
    have h1 : y + z + t = 1 := by 
      rw [hx1] at h₀ 
      linarith 
    have h2 : y * z + t = 2 := by 
      rw [hx1] at h₁ 
      linarith 
    have h3 : z * t + y = -2 := by 
      rw [hx1] at h₂ 
      linarith 
    -- Now prove ht : t = 1 - y - z 
    have ht : t = 1 - y - z := by 
      nlinarith 
    -- From h_eq1: y * z - y - z = 1
    have h_eq1 : y * z - y - z = 1 := by 
      rw [ht] at h2 
      nlinarith 
    -- From h_eq2 : z * (1 - y - z) + y = -2
    have h_eq2 : z * (1 - y - z) + y = -2 := by 
      rw [ht] at h3 
      linarith 
    have hz : z = -1 := by
      have hyz1 : z ^ 2 = 1 := by 
        nlinarith [sq_nonneg (y + z), sq_nonneg (z + 1)]
      have h_eq3 : z = 1 ∨ z = -1 := by
        rw [sq_eq_one_iff] at hyz1 
        tauto 
      cases' h_eq3 with h11 h22 
      · -- Case z = 1
        exfalso 
        have h111 : z = 1 := h11 
        rw [h111] at h_eq1 
        nlinarith 
      · 
        linarith 
    -- Now prove y = 0 
    have hy0 : y = 0 := by 
      rw [hz] at h_eq1 
      nlinarith 
    -- Now prove t = 2 
    have ht2 : t = 2 := by 
      rw [hz] at ht 
      linarith [hy0] 
    -- Final substitution 
    simp [Prod.ext_iff, hx1, hy0, hz, ht2]
    all_goals linarith 
  · -- Case y - t = 0, so y = t 
    have h_eq : y = t := by linarith 
    rw [show t = y by linarith [h_eq]] at h₂ h₃ 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 0), sq_nonneg (z + 1), sq_nonneg (y - 0), sq_nonneg (z + 1)]