import Mathlib

theorem algebra_198250 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x) (h₁ : f 1 = 2)
    (h₂ : ∀ x y, x * y ≠ 0 → f (Real.sqrt (x ^ 2 + y ^ 2)) = f x * f y / (f x + f y)) :
    f 5 = 2 / 25 := by

  have h3 : f (Real.sqrt 2) = 1 := by
    have h4 : f (Real.sqrt (1 ^ 2 + 1 ^ 2)) = f 1 * f 1 / (f 1 + f 1) := by
      apply h₂ 1 1
      norm_num
    have h5 : Real.sqrt (1 ^ 2 + 1 ^ 2) = Real.sqrt 2 := by norm_num
    rw [h5] at h4
    rw [h₁] at h4
    norm_num at h4 ⊢
    linarith

  have h6 : f (Real.sqrt 3) = 2 / 3 := by
    have h7 : f (Real.sqrt (1 ^ 2 + (Real.sqrt 2) ^ 2)) = f 1 * f (Real.sqrt 2) / (f 1 + f (Real.sqrt 2)) := by
      apply h₂ 1 (Real.sqrt 2)
      have h8 : (1 : ℝ) * Real.sqrt 2 ≠ 0 := by
        have h9 : Real.sqrt 2 > 0 := by
          positivity
        nlinarith
      exact h8
    have h10 : Real.sqrt (1 ^ 2 + (Real.sqrt 2) ^ 2) = Real.sqrt 3 := by
      have h11 : (1 : ℝ) ^ 2 + (Real.sqrt 2) ^ 2 = (3 : ℝ) := by
        have h12 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
        nlinarith [h12]
      rw [h11]
    rw [h10] at h7
    rw [h₁, h3] at h7
    norm_num at h7 ⊢
    linarith

  have h8 : f (2 : ℝ) = 1 / 2 := by
    have h9 : f (Real.sqrt ((Real.sqrt 2 : ℝ) ^ 2 + (Real.sqrt 2 : ℝ) ^ 2)) = f (Real.sqrt 2) * f (Real.sqrt 2) / (f (Real.sqrt 2) + f (Real.sqrt 2)) := by
      apply h₂ (Real.sqrt 2) (Real.sqrt 2)
      have h10 : Real.sqrt 2 * Real.sqrt 2 ≠ 0 := by
        have h11 : Real.sqrt 2 > 0 := by positivity
        nlinarith
      exact h10
    have h12 : Real.sqrt ((Real.sqrt 2 : ℝ) ^ 2 + (Real.sqrt 2 : ℝ) ^ 2) = (2 : ℝ) := by
      have h13 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      have h14 : (Real.sqrt 2 : ℝ) ^ 2 + (Real.sqrt 2 : ℝ) ^ 2 = (4 : ℝ) := by
        nlinarith [h13]
      rw [h14]
      have h15 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h15]
    rw [h12] at h9
    rw [h3] at h9
    norm_num at h9 ⊢
    linarith

  have h10 : f (Real.sqrt 5) = 2 / 5 := by
    have h11 : f (Real.sqrt (1 ^ 2 + (2 : ℝ) ^ 2)) = f 1 * f (2 : ℝ) / (f 1 + f (2 : ℝ)) := by
      apply h₂ 1 (2 : ℝ)
      norm_num
    have h12 : Real.sqrt (1 ^ 2 + (2 : ℝ) ^ 2) = Real.sqrt 5 := by
      norm_num
    rw [h12] at h11
    rw [h₁, h8] at h11
    norm_num at h11 ⊢
    linarith

  have h13 : f (Real.sqrt 6) = 1 / 3 := by
    have h14 : f (Real.sqrt ((Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 3 : ℝ) ^ 2)) = f (Real.sqrt 3) * f (Real.sqrt 3) / (f (Real.sqrt 3) + f (Real.sqrt 3)) := by
      apply h₂ (Real.sqrt 3) (Real.sqrt 3)
      have h15 : Real.sqrt 3 * Real.sqrt 3 ≠ 0 := by
        have h16 : Real.sqrt 3 > 0 := by positivity
        nlinarith
      exact h15
    have h17 : Real.sqrt ((Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 3 : ℝ) ^ 2) = Real.sqrt 6 := by
      have h18 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h19 : (Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 3 : ℝ) ^ 2 = (6 : ℝ) := by
        nlinarith [h18]
      rw [h19]
    rw [h17] at h14
    rw [h6] at h14
    norm_num at h14 ⊢
    linarith

  have h14 : f (3 : ℝ) = 2 / 9 := by
    have h15 : f (Real.sqrt ((Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 6 : ℝ) ^ 2)) = f (Real.sqrt 3) * f (Real.sqrt 6) / (f (Real.sqrt 3) + f (Real.sqrt 6)) := by
      apply h₂ (Real.sqrt 3) (Real.sqrt 6)
      have h16 : Real.sqrt 3 * Real.sqrt 6 ≠ 0 := by
        have h17 : Real.sqrt 3 > 0 := by positivity
        have h18 : Real.sqrt 6 > 0 := by positivity
        nlinarith
      exact h16
    have h19 : Real.sqrt ((Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 6 : ℝ) ^ 2) = (3 : ℝ) := by
      have h20 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h21 : (Real.sqrt 6 : ℝ) ^ 2 = (6 : ℝ) := Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)
      have h22 : (Real.sqrt 3 : ℝ) ^ 2 + (Real.sqrt 6 : ℝ) ^ 2 = (9 : ℝ) := by
        nlinarith [h20, h21]
      rw [h22]
      have h23 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h23]
    rw [h19] at h15
    rw [h6, h13] at h15
    norm_num at h15 ⊢
    linarith

  have h17 : f (4 : ℝ) = 1 / 8 := by
    have h42 : f (2 * Real.sqrt 2 : ℝ) = 1 / 4 := by
      have h9 : f (Real.sqrt ((2 : ℝ) ^ 2 + (2 : ℝ) ^ 2)) = f (2 : ℝ) * f (2 : ℝ) / (f (2 : ℝ) + f (2 : ℝ)) := by
        apply h₂ 2 2
        norm_num
      have h10 : Real.sqrt ((2 : ℝ) ^ 2 + (2 : ℝ) ^ 2) = (2 * Real.sqrt 2 : ℝ) := by
        have h11 : (2 : ℝ) ^ 2 + (2 : ℝ) ^ 2 = (8 : ℝ) := by norm_num
        rw [h11]
        have h12 : Real.sqrt (8 : ℝ) = (2 * Real.sqrt 2 : ℝ) := by
          have h13 : Real.sqrt (8 : ℝ) = Real.sqrt (4 * 2 : ℝ) := by
            norm_num
          rw [h13]
          have h14 : Real.sqrt (4 * (2 : ℝ)) = Real.sqrt (4 : ℝ) * Real.sqrt (2 : ℝ) := by
            rw [Real.sqrt_mul (by norm_num)]
          rw [h14]
          have h15 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h15]
          all_goals
            ring_nf
        rw [h12]
      rw [h10] at h9
      rw [h8] at h9
      norm_num at h9 ⊢
      linarith
    have h44 : f (Real.sqrt ((2 * Real.sqrt 2 : ℝ) ^ 2 + (2 * Real.sqrt 2 : ℝ) ^ 2)) = f (2 * Real.sqrt 2 : ℝ) * f (2 * Real.sqrt 2 : ℝ) / (f (2 * Real.sqrt 2 : ℝ) + f (2 * Real.sqrt 2 : ℝ)) := by
      apply h₂ (2 * Real.sqrt 2) (2 * Real.sqrt 2)
      have h43 : (2 * Real.sqrt 2 : ℝ) * (2 * Real.sqrt 2 : ℝ) ≠ 0 := by
        have h44 : Real.sqrt 2 > 0 := by positivity
        nlinarith
      exact h43
    have h45 : Real.sqrt ((2 * Real.sqrt 2 : ℝ) ^ 2 + (2 * Real.sqrt 2 : ℝ) ^ 2) = (4 : ℝ) := by
      have h46 : (2 * Real.sqrt 2 : ℝ) ^ 2 + (2 * Real.sqrt 2 : ℝ) ^ 2 = (16 : ℝ) := by
        have h47 : (2 * Real.sqrt 2 : ℝ) ^ 2 = (8 : ℝ) := by
          calc
            (2 * Real.sqrt 2 : ℝ) ^ 2 = 4 * (Real.sqrt 2 : ℝ) ^ 2 := by ring
            _ = 4 * (2 : ℝ) := by
              rw [Real.sq_sqrt]
              all_goals norm_num
            _ = (8 : ℝ) := by norm_num
        nlinarith [h47]
      rw [h46]
      have h48 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      rw [h48]
    rw [h45] at h44
    rw [h42] at h44
    norm_num at h44 ⊢
    linarith

  have h60 : f (Real.sqrt ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2)) = f (3 : ℝ) * f (4 : ℝ) / (f (3 : ℝ) + f (4 : ℝ)) := by
    apply h₂ 3 4
    norm_num
  have h61 : Real.sqrt ((3 : ℝ) ^ 2 + (4 : ℝ) ^ 2) = (5 : ℝ) := by
    have h62 : (3 : ℝ) ^ 2 + (4 : ℝ) ^ 2 = (25 : ℝ) := by
      norm_num
    rw [h62]
    have h63 : Real.sqrt (25 : ℝ) = (5 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h63]
  rw [h61] at h60
  rw [h14, h17] at h60
  norm_num at h60 ⊢
  linarith