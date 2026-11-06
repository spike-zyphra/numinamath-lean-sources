import Mathlib

theorem algebra_310361 (a b c : ℝ) (h : ∀ x : ℝ, a * x ^ 2 + b * x + c ≥ 0)
    (ha : a ≤ b) :
    (b - a) / (a + b + c) ≤ 1 / 3 := by 
  by_cases h8 : a + b + c > 0
  · -- Assume a + b + c > 0 
    have h9 : 3 * (b - a) ≤ a + b + c := by
      have h1 := h (-2)
      have h2 := h (-1)
      have h3 := h 0 
      have h4 := h 1 
      have h5 := h 2 
      nlinarith 
    have h10 : (b - a) / (a + b + c) ≤ 1 / 3 := by 
      apply (div_le_iff₀ (by linarith)).mpr 
      nlinarith [h9]
    exact h10 
  · -- Assume a + b + c ≤ 0 
    -- First, establish a + b + c = 0
    have h9 : a + b + c = 0 := by
      have h1 := h 1
      have h2 := h (-1: ℝ)
      have h3 := h 0 
      have h4 := h 2 
      have h5 := h (-2: ℝ)
      nlinarith 
    -- Second, establish b = 0 
    have hb1 : b = 0 := by
      have h1 := h (-1: ℝ)
      have h2 := h (1: ℝ)
      have h1' : c = - a - b := by linarith 
      rw [h1'] at h1
      have h3 := h 2 
      have h4 : c = - a - b := by linarith 
      rw [h4] at h3 
      have h6 := h 0 
      have h7 := h (-2: ℝ)
      nlinarith 
    -- Third, establish a = 0 
    have ha1 : a = 0 := by 
      have hb2 : c = -a := by nlinarith [h9, hb1]
      have h14 := h (-2: ℝ)
      simp only [hb1] at h14
      nlinarith [hb2, ha, hb1, h14]
    -- Fourth, establish c = 0 
    have hc1 : c = 0 := by
      nlinarith [h9, ha1, hb1]
    rw [ha1, hb1, hc1] 
    norm_num