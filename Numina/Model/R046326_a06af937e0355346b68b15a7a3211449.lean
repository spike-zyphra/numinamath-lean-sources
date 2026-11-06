import Mathlib

theorem algebra_125976 (f : ℝ → ℝ) (k : ℝ) (hf : f = fun x => k * x ^ 2 + 2 * k * x + 1)
    (hmax : ∃ x ∈ Set.Icc (-3) 2, f x = 4) (hmax' : ∀ x ∈ Set.Icc (-3) 2, f x ≤ 4) :
    k = -3 ∨ k = 3 / 8 := by 
  have h1 := hmax' (-3) (by norm_num) 
  simp [hf] at h1 
  have h2 := hmax' (2) (by norm_num)
  simp [hf] at h2 
  have h3 := hmax' (-1) (by norm_num) 
  simp [hf] at h3 
  rcases hmax with ⟨x, hx, hfx⟩ 
  simp [hf] at hfx 
  have hx1 : -3 ≤ x := by 
    have h : x ∈ Set.Icc (-3 : ℝ) 2 := hx 
    simp at h ⊢ 
    linarith 
  have hx2 : x ≤ 2 := by 
    have h : x ∈ Set.Icc (-3 : ℝ) 2 := hx 
    simp at h ⊢ 
    linarith 
  by_cases h4 : k < 0 
  · -- Case k < 0, parabola opens downwards 
    by_cases h5 : x = -1 
    · -- Assume x = -1 
      rw [h5] at hfx 
      have h6 : k = -3 := by 
        nlinarith 
      left 
      linarith 
    · -- Assume x ≠ -1 
      have h6 : x ≠ -1 := h5 
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x + 3), sq_nonneg (x - 2), 
          sq_nonneg (k + 3), sq_nonneg ((x + 1) * (k)), 
            sq_pos_of_ne_zero (show ((k) : ℝ) ≠ 0 by nlinarith), 
              sq_pos_of_ne_zero (show ((x + 1) : ℝ) ≠ 0 by 
                intro h 
                apply h6 
                linarith 
              )
          ]
  · -- Assume k ≥ 0 
    have h_k_nonneg : k ≥ 0 := by linarith 
    by_cases h_k_zero : k = 0 
    · -- Assume k = 0 
      rw [h_k_zero] at hfx 
      nlinarith 
    · -- Assume k > 0 
      have h_k_pos : k > 0 := by 
        by_contra h 
        push_neg at h 
        have : k = 0 := by 
          nlinarith 
        contradiction 
      have h7 : k = 3 / 8 := by 
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 3), sq_nonneg (x + 1), 
            sq_nonneg (k - 3 / 8), sq_nonneg ((x + 1) * (k)), 
              mul_nonneg (show (0 : ℝ) ≤ 2 - x by linarith) 
                (show (0 : ℝ) ≤ x + 3 by linarith) 
          ]
      right 
      linarith