import Mathlib

theorem algebra_9035 {f : ℝ → ℝ} (hf : f = fun x => √(4 - x ^ 2) / (|x + 3| - 3)) (a : ℝ) (dom_a : 4 - a ^ 2 ≥ 0 ∧ |a + 3| - 3 ≠ 0)
    (ha : f a = -4) : f (-a) = 4 := by 
  have h1 : 4 - a ^ 2 ≥ 0 := dom_a.1
  have h2 : |a + 3| - 3 ≠ 0 := dom_a.2
  have h3 : f a = √(4 - a ^ 2) / (|a + 3| - 3) := by 
    rw [hf]
  have eq1 : √(4 - a ^ 2) / (|a + 3| - 3) = -4 := by 
    rw [show f a = √(4 - a ^ 2) / (|a + 3| - 3) by rw [h3]] at ha 
    tauto 
  -- Actually simple compute f(-a) does the relevant.
  have h8 : f (-a) = √(4 - (-a) ^ 2) / (|-a + 3| - 3) := by 
    rw [hf] 
    all_goals ring_nf 
  have hx1 : |-a + 3| = -a + 3 := by 
    have ht1 : -a + 3 > 0 := by 
      nlinarith [Real.sqrt_nonneg (4 - a^2), Real.sq_sqrt (show (4 - a ^ 2) ≥ 0 by linarith)]
    apply abs_of_pos
    all_goals linarith 
  have hx2 : |-a + 3| - 3 = -a := by
    rw [ hx1 ]
    all_goals 
    ring_nf 
  have hx3 : √(4 - (-a) ^ 2) = √(4 - a ^ 2) := by 
    ring_nf 
  rw [ h8, hx2, hx3 ]
  have h9 : √(4 - a ^ 2) / (-a ) = 4 := by 
    have ht1 : |a + 3| = a + 3 := by
      apply abs_of_nonneg 
      nlinarith [h1]
    have ht2 : |a + 3| - 3 = a := by
      rw [ht1]
      all_goals linarith 
    have ht3 : √(4 - a ^ 2) = -4 * a := by 
      have ht4 : √(4 - a ^ 2) / (|a + 3| - 3) = -4 := by
        linarith [ eq1 ]
      rw [ ht2 ] at ht4 
      have ha7 : a ≠ 0 := by 
        by_contra h
        have ht0 : a = (0 : ℝ) := by linarith 
        rw [ ht0 ] at h2
        norm_num at h2 
      field_simp [ha7] at ht4 ⊢ 
      all_goals nlinarith 
    rw [ ht3 ]
    have ha2 : a ≠ 0 := by 
      by_contra h
      rw [ h ] at h2 
      norm_num at h2 
    field_simp [ha2]
    all_goals nlinarith 
  linarith [h9]