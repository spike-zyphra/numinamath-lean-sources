import Mathlib

theorem algebra_10673 {f g : ℝ → ℝ} (hf : f 1 = 2 * 2) (hg : g.RightInverse f)
    (hfg : ∀ x, f x = g x / 2) :
    ∃! x, ∃! y, f x = y ∧ g y = x ∧ x + y = 9 / 2 := by

  have h6 : g 1 = (8 : ℝ) := by
    have h7 : f 1 = 4 := by
      linarith [hf]
    have h8 : f 1 = g 1 / 2 := by
      specialize hfg 1
      simpa using hfg
    rw [h7] at h8
    linarith

  have h7 : f 8 = (1 : ℝ) := by
    have h8 : f (g 1) = (1 : ℝ) := by 
      apply hg 
    rw [show g 1 = (8 : ℝ) by linarith [h6] ] at h8
    linarith

  have h8 : g 8 = (2 : ℝ) := by
    have h9 : f 8 = g 8 / 2 := by
      specialize hfg 8
      simpa using hfg
    rw [show f 8 = (1 : ℝ) by linarith [h7] ] at h9
    linarith

  have h9 : f 2 = (8 : ℝ) := by
    have h10 : f (g 8) = (8 : ℝ) := by 
      apply hg 
    rw [show g 8 = (2 : ℝ) by linarith [h8] ] at h10
    linarith

  have h10 : g 2 = (16 : ℝ) := by
    have h11 : f 2 = g 2 / 2 := by
      specialize hfg 2
      simpa using hfg
    rw [show f 2 = (8 : ℝ) by linarith [h9] ] at h11
    linarith

  have h11 : f 16 = (2 : ℝ) := by
    have h12 : f (g 2) = (2 : ℝ) := by 
      apply hg 
    rw [show g 2 = (16 : ℝ) by linarith [h10] ] at h12
    linarith

  have h12 : g 16 = (4 : ℝ) := by
    have h13 : f 16 = g 16 / 2 := by
      specialize hfg 16
      simpa using hfg
    rw [show f 16 = (2 : ℝ) by linarith [h11] ] at h13
    linarith

  have h13 : f 4 = (16 : ℝ) := by
    have h14 : f (g 16) = (16 : ℝ) := by
      apply hg 
    rw [show g 16 = (4 : ℝ) by linarith [h12] ] at h14
    linarith

  have h14 : g 4 = (32 : ℝ) := by
    have h15 : f 4 = g 4 / 2 := by
      specialize hfg 4
      simpa using hfg
    rw [show f 4 = (16 : ℝ) by linarith [h13] ] at h15
    linarith

  have h15 : f 32 = (4 : ℝ) := by
    have h16 : f (g 4) = (4 : ℝ) := by
      apply hg 
    rw [show g 4 = (32 : ℝ) by linarith [h14] ] at h16
    linarith

  have h16 : g 32 = (8 : ℝ) := by
    have h17 : f 32 = g 32 / 2 := by
      specialize hfg 32
      simpa using hfg
    rw [show f 32 = (4 : ℝ) by linarith [h15] ] at h17
    linarith

  have h17 : f 8 = (32 : ℝ) := by
    have h18 : f (g 32) = (32 : ℝ) := by
      apply hg 
    rw [show g 32 = (8 : ℝ) by linarith [h16] ] at h18
    linarith

  linarith -- This is sufficient, as it will notice the right sides have contradictory values