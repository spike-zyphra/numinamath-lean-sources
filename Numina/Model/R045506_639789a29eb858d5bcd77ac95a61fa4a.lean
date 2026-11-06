import Mathlib

theorem algebra_147892 (a : ℝ) :
    (∃! x : ℝ, 2 ^ abs (2 * x - 2) - a * Real.cos (1 - x) = 0) ↔ a = 1 := by
  constructor
  · -- Assume there is a unique solution, prove a = 1
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have h1 : 2 ^ abs (2 * x - 2) - a * Real.cos (1 - x) = 0 := hx1
    have h2 : 2 ^ abs (2 * (2 - x) - 2) - a * Real.cos (1 - (2 - x)) = 0 := by
      have eq1 : abs (2 * (2 - x) - 2) = abs (2 * x - 2) := by
        have h4 : 2 * (2 - x) - 2 = -(2 * x - 2) := by
          ring
        rw [h4]
        rw [abs_neg]
      have eq2 : Real.cos (1 - (2 - x)) = Real.cos (1 - x) := by
        have h5 : 1 - (2 - x) = -(1 - x) := by
          ring
        rw [h5]
        have h6 : Real.cos (-(1 - x)) = Real.cos (1 - x) := by 
          rw [Real.cos_neg]
        linarith [h6]
      have eq3 : (2 : ℝ) ^ abs (2 * (2 - x) - 2) = (2 : ℝ) ^ abs (2 * x - 2) := by 
        rw [eq1]
      have eq4 : (2 : ℝ) ^ abs (2 * (2 - x) - 2) - a * Real.cos (1 - (2 - x)) = (2 : ℝ) ^ abs (2 * x - 2) - a * Real.cos (1 - x) := by 
        rw [eq3, eq2]
      linarith [h1, eq4]
    have h3 : (2 - x) = x := by 
      apply hx2 (2 - x) h2 
    have h4 : x = 1 := by 
      linarith 
    rw [h4] at h1 
    norm_num [abs_zero, Real.cos_zero] at h1 
    linarith 
  · -- Assume a = 1, prove there is a unique solution
    intro ha 
    use 1 
    constructor 
    · -- Show x = 1 is a solution 
      rw [ha]
      norm_num [abs_zero, Real.cos_zero] 
    · -- Show it's unique 
      intro y hy 
      rw [ha] at hy 
      have h1 : (2 : ℝ) ^ abs (2 * y - 2) - Real.cos (1 - y) = 0 := by 
        simpa using hy 
      have h2 : (2 : ℝ) ^ abs (2 * y - 2) = Real.cos (1 - y) := by 
        linarith 
      have h3 : (2 : ℝ) ^ abs (2 * y - 2) ≥ 1 := by 
        have h4 : abs (2 * y - 2) ≥ (0 : ℝ) := by 
          apply abs_nonneg 
        have h5 : (2 : ℝ) ^ abs (2 * y - 2) ≥ (2 : ℝ) ^ (0 : ℝ) := by 
          apply Real.rpow_le_rpow_of_exponent_le 
          all_goals linarith 
        have h6 : (2 : ℝ) ^ (0 : ℝ) = 1 := by 
          simp 
        linarith [h5, h6] 
      have h4 : Real.cos (1 - y) ≥ 1 := by 
        linarith [h2, h3] 
      have h5 : Real.cos (1 - y) ≤ 1 := by 
        apply Real.cos_le_one 
      have h6 : Real.cos (1 - y) = 1 := by 
        linarith 
      have h7 : abs (2 * y - 2) = 0 := by 
        have h8 : (2 : ℝ) ^ abs (2 * y - 2) = 1 := by 
          linarith [h2, h6] 
        by_cases h : abs (2 * y - 2) > (0 : ℝ)
        · -- Assume abs (2 * y - 2) > 0 
          have h10 : (2 : ℝ) ^ abs (2 * y - 2) > (1 : ℝ) := by 
            have h11 : abs (2 * y - 2) > (0 : ℝ) := h 
            have h12 : (2 : ℝ) ^ abs (2 * y - 2) > (2 : ℝ) ^ (0 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals linarith 
            have h13 : (2 : ℝ) ^ (0 : ℝ) = 1 := by 
              simp 
            linarith [h12, h13] 
          linarith [h8, h10] 
        · -- Assume ¬(abs (2 * y - 2) > 0) 
          have h15 : abs (2 * y - 2) ≤ (0 : ℝ) := by 
            linarith 
          have h16 : abs (2 * y - 2) = (0 : ℝ) := by 
            linarith [abs_nonneg (2 * y - 2), h15] 
          linarith 
      have h8 : 2 * y - 2 = (0 : ℝ) := by 
        rwa [abs_eq_zero] at h7 
      linarith