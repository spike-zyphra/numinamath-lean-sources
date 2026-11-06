import Mathlib

theorem algebra_102783 {f : ℝ → ℝ} (hodd : Odd f) (hf1 : ∀ x y, f (x + y) = f x + f y)
    (hf2 : ∀ x > 0, f x < 0) (hf3 : f 1 = -2) :
    IsGreatest (Set.image f (Set.Icc (-3) 3)) 6 ∧ IsLeast (Set.image f (Set.Icc (-3) 3)) (-6) := by

  have h0 : f 0 = 0 := by 
    have h0 : f (0 + 0) = f 0 + f 0 := hf1 0 0
    simp at h0 
    linarith

  have h1 : f (-1) = 2 := by
    have hodd1 : f (-1) = -f 1 := by
      have h10 : f (1 + (-1)) = f 1 + f (-1) := hf1 1 (-1) 
      have h11 : f (1 + (-1)) = f 0 := by 
        ring_nf 
      rw [h11] at h10 
      rw [h0] at h10
      linarith 
    rw [hf3] at hodd1 
    linarith

  have h2 : f 2 = -4 := by
    have h20 : f (1 + 1) = f 1 + f 1 := hf1 1 1 
    rw [show (1 + 1 : ℝ) = (2 : ℝ) by norm_num] at h20 
    rw [hf3] at h20 
    linarith

  have h3 : f 3 = -6 := by
    have h30 : f (2 + 1) = f 2 + f 1 := hf1 2 1 
    rw [show (2 + 1 : ℝ) = (3 : ℝ) by norm_num] at h30 
    rw [h2, hf3] at h30 
    linarith

  have h3_neg : f (-3) = 6 := by
    have h30 : f (3 + (-3)) = f 3 + f (-3) := hf1 3 (-3) 
    have h31 : f (3 + (-3)) = f 0 := by 
      ring_nf 
    rw [h31] at h30 
    rw [h0] at h30 
    rw [h3] at h30 
    linarith

  constructor 
  · -- We need to prove 6 is greatest in the image of f on [-3, 3]
    constructor 
    · -- Show 6 is attained at -3 
      use -3 
      constructor 
      · -- Show -3 ∈ [-3, 3] 
        norm_num 
      · -- Show f(-3) = 6 
        rw [h3_neg] 
    · -- Show for all y in the image, y ≤ 6 
      intro y 
      rintro ⟨x, hx, hfx⟩ 
      have hx1 : -3 ≤ x := by
        have h1 : x ∈ Set.Icc (-3) 3 := by
          simpa using hx
        exact h1.1 
      have hx2 : x ≤ 3 := by
        have h1 : x ∈ Set.Icc (-3) 3 := by
          simpa using hx
        exact h1.2 
      have h4 : f x ≤ 6 := by 
        have h9 : x ≤ 3 := by linarith 
        have h40 : x + 3 ≥ 0 := by 
          nlinarith 
        have h41 : f (x + 3) ≤ 0 := by 
          have h18 : x + 3 ≥ 0 := h40 
          by_cases h21 : x + 3 > 0 
          · -- x + 3 > 0 
            have h43 : f (x + 3) < 0 := by 
              apply hf2 
              all_goals 
                nlinarith 
            linarith 
          · -- x + 3 = 0 
            have h73 : x + 3 = (0 : ℝ) := by nlinarith [show x + 3 ≥ 0 by linarith] 
            have h4_5 : f (x + 3) = 0 := by 
              rw [show x + 3 = (0 : ℝ) by nlinarith [h73]] 
              linarith [h0] 
            linarith [h4_5] 
        have h44 : f (x + 3) = f x + f 3 := by 
          rw [← hf1 x 3] 
          all_goals 
            ring 
        rw [h3] at h44 
        linarith 
      linarith [hfx, h4] 
  · -- We need to prove -6 is the least element in the image 
    constructor 
    · -- Show -6 is attained at 3 
      use 3 
      constructor 
      · -- Show 3 ∈ [-3, 3] 
        norm_num 
      · -- Show f(3) = -6 
        rw [h3] 
    · -- Show for all y in the image, -6 ≤ y 
      intro y 
      rintro ⟨x, hx, hfx⟩ 
      have hx1 : -3 ≤ x := by
        have h1 : x ∈ Set.Icc (-3) 3 := by
          simpa using hx
        exact h1.1 
      have hx2 : x ≤ 3 := by
        have h1 : x ∈ Set.Icc (-3) 3 := by
          simpa using hx
        exact h1.2 
      have h44 : f x ≥ -6 := by
        have h13 : x + (3 - x) = (3 : ℝ) := by ring
        have h14 : f (x + (3 - x)) = f x + f (3 - x) := hf1 x (3 - x)
        rw [show x + (3 - x) = (3 : ℝ) by linarith] at h14
        rw [h3] at h14
        have h15 : 3 - x ≥ 0 := by 
          nlinarith 
        have h19 : f (3 - x) ≤ 0 := by 
          by_cases h21 : 3 - x > 0 
          · -- 3 - x > 0 
            have h22 : f (3 - x) < 0 := by 
              apply hf2 
              all_goals linarith 
            linarith 
          · -- 3 - x = 0 
            have h23 : 3 - x = 0 := by 
              nlinarith 
            rw [h23] 
            linarith [h0] 
        linarith 
      linarith [hfx, h44]