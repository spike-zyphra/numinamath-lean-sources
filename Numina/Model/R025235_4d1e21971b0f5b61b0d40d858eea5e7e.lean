import Mathlib


theorem algebra_12273 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 2) = -f x)
    (hf' : ∀ x ∈ Set.Icc 0 1, f x = 2 * x) :
    f (10 * Real.sqrt 3) = 36 - 20 * Real.sqrt 3 := by
  have h4 : ∀ x, f (x + 4) = f x := by
    intro x
    calc
      f (x + 4) = f (x + 2 + 2) := by ring_nf
      _ = -f (x + 2) := by rw [hf]
      _ = -(-f x) := by rw [hf x]
      _ = f x := by ring

  have h1 : f (10 * Real.sqrt 3) = f (10 * Real.sqrt 3 - 16) := by
    calc
      f (10 * Real.sqrt 3) = f (10 * Real.sqrt 3 - 16 + 16) := by ring_nf
      _ = f (10 * Real.sqrt 3 - 16) := by
        have h22 : f ((10 * Real.sqrt 3 - 16) + 16) = f (10 * Real.sqrt 3 - 16) := by
          have h23 : f ((10 * Real.sqrt 3 - 16) + 16) = f ((10 * Real.sqrt 3 - 16) + 12) := by
            have h24 : f (((10 * Real.sqrt 3 - 16) + 12) + 4) = f ((10 * Real.sqrt 3 - 16) + 12) := by
              rw [h4 ((10 * Real.sqrt 3 - 16) + 12)]
            have h25 : f (((10 * Real.sqrt 3 - 16) + 12) + 4) = f ((10 * Real.sqrt 3 - 16) + 16) := by ring_nf
            have h26 : f ((10 * Real.sqrt 3 - 16) + 16) = f ((10 * Real.sqrt 3 - 16) + 12) := by
              linarith [h24, h25]
            exact h26
          -- now proving (Y + 12) \eq (Y + 8)
          have h27 : f ((10 * Real.sqrt 3 - 16) + 12) = f ((10 * Real.sqrt 3 - 16) + 8) := by
            have h28 : f (((10 * Real.sqrt 3 - 16) + 8) + 4) = f ((10 * Real.sqrt 3 - 16) + 8) := by
              rw [h4 ((10 * Real.sqrt 3 - 16) + 8)]
            have h29 : f (((10 * Real.sqrt 3 - 16) + 8) + 4) = f ((10 * Real.sqrt 3 - 16) + 12) := by ring_nf
            have h30 : f ((10 * Real.sqrt 3 - 16) + 12) = f ((10 * Real.sqrt 3 - 16) + 8) := by
              linarith [h28, h29]
            linarith
          -- now proving (Y + 8) \eq (Y + 4)
          have h31 : f ((10 * Real.sqrt 3 - 16) + 8) = f ((10 * Real.sqrt 3 - 16) + 4) := by
            have h32 : f (((10 * Real.sqrt 3 - 16) + 4) + 4) = f ((10 * Real.sqrt 3 - 16) + 4) := by
              rw [h4 ((10 * Real.sqrt 3 - 16) + 4)]
            have h33 : f (((10 * Real.sqrt 3 - 16) + 4) + 4) = f ((10 * Real.sqrt 3 - 16) + 8) := by ring_nf
            have h34 : f ((10 * Real.sqrt 3 - 16) + 8) = f ((10 * Real.sqrt 3 - 16) + 4) := by
              linarith [h32, h33]
            linarith
          -- now proving (Y + 4) \eq (Y)
          have h35 : f ((10 * Real.sqrt 3 - 16) + 4) = f (10 * Real.sqrt 3 - 16) := by
            have h36 : f ((10 * Real.sqrt 3 - 16) + 4) = f (10 * Real.sqrt 3 - 16) := by
              rw [h4 (10 * Real.sqrt 3 - 16)]
            exact h36
          -- putting them all together
          have h37 : f ((10 * Real.sqrt 3 - 16) + 16) = f (10 * Real.sqrt 3 - 16) := by
            linarith [h23, h27, h31, h35]
          exact h37
        exact h22

  have h3 : 1 < 10 * Real.sqrt 3 - 16 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h4' : 10 * Real.sqrt 3 - 16 < 2 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h5 : f (10 * Real.sqrt 3 - 16) = 4 - 2 * (10 * Real.sqrt 3 - 16) := by
    have h5' : f (10 * Real.sqrt 3 - 16) = f (2 - (10 * Real.sqrt 3 - 16)) := by
      have h8 : f (10 * Real.sqrt 3 - 16) = -f ((10 * Real.sqrt 3 - 16) - 2) := by
        have h11 : f ((10 * Real.sqrt 3 - 16) - 2 + 2) = -f ((10 * Real.sqrt 3 - 16) - 2) := by
          rw [hf ((10 * Real.sqrt 3 - 16) - 2)]
        have h12 : f ((10 * Real.sqrt 3 - 16) - 2 + 2) = f (10 * Real.sqrt 3 - 16) := by
          ring_nf
        rw [h12] at h11
        linarith
      have h9 : f ((10 * Real.sqrt 3 - 16) - 2) = -f (2 - (10 * Real.sqrt 3 - 16)) := by
        have h14 : (10 * Real.sqrt 3 - 16) - 2 = - (2 - (10 * Real.sqrt 3 - 16)) := by
          linarith
        rw [h14]
        have h15 : f (- (2 - (10 * Real.sqrt 3 - 16)) ) = -f (2 - (10 * Real.sqrt 3 - 16)) := by
          rw [hodd (2 - (10 * Real.sqrt 3 - 16)) ]
        linarith
      linarith
    have h6 : 2 - (10 * Real.sqrt 3 - 16) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      ·
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      ·
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h7 : f (2 - (10 * Real.sqrt 3 - 16)) = 2 * (2 - (10 * Real.sqrt 3 - 16)) := by
      apply hf'
      exact h6
    rw [h5', h7]
    all_goals nlinarith

  rw [h1, h5]
  all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]