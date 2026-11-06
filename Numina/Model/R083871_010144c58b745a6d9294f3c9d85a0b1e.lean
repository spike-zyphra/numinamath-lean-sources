import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8446 {f g : ℝ → ℝ} (hf : f = λ x => 2^x - 2^(-x)) (hg : g.RightInverse f)
  (x : ℝ) : abs (g (x - 1)) < 1 ↔ -1 / 2 < x ∧ x < 5 / 2 := by
    have hg2 : ∀ y, f (g y) = y := by 
      intro y
      apply hg
    have h5 : f 1 = 3 / 2 := by 
      rw [hf]
      norm_num
    have h6 : f (-1) = -3 / 2 := by 
      rw [hf]
      norm_num
    rw [abs_lt]
    constructor
    · -- Forward implication: |g(x-1)| < 1 → -1/2 < x ∧ x < 5/2
      rintro ⟨h1, h2⟩
      have h3 : x - 1 < f 1 := by
        have h4 : g (x - 1) < 1 := h2
        have h' : f (g (x - 1)) < f 1 := by 
          have h5 : g (x - 1) < 1 := h2
          have h6 : f (g (x - 1)) = x - 1 := by
            rw [hg2 (x - 1)]
          have hf1 : StrictMono f := by
            intro x y hxy
            rw [hf]
            simp at *
            have h1 : (2 : ℝ) ^ x < (2 : ℝ) ^ y := by 
              apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy
            have h2 : (2 : ℝ) ^ (-x) > (2 : ℝ) ^ (-y) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hxy)
            all_goals linarith 
          have h7 : f (g (x - 1)) < f 1 := hf1 h5
          linarith 
        have h8 : f (g (x - 1)) = x - 1 := by 
          rw [hg2 (x - 1)]
        linarith 
      have h4 : x - 1 > f (-1) := by
        have h5 : g (x - 1) > -1 := h1
        have h' : f (g (x - 1)) > f (-1) := by 
          have h5 : g (x - 1) > -1 := h1
          have h6 : f (g (x - 1)) = x - 1 := by
            rw [hg2 (x - 1)]
          have hf1 : StrictMono f := by
            intro x y hxy
            rw [hf]
            simp at *
            have h1 : (2 : ℝ) ^ x < (2 : ℝ) ^ y := by 
              apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy
            have h2 : (2 : ℝ) ^ (-x) > (2 : ℝ) ^ (-y) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hxy)
            all_goals linarith 
          have h7 : f (g (x - 1)) > f (-1) := hf1 h5
          linarith 
        have h8 : f (g (x - 1)) = x - 1 := by 
          rw [hg2 (x - 1)]
        linarith 
      have h7 : x < 5 / 2 := by
        rw [h5] at h3 
        linarith 
      have h8 : -1 / 2 < x := by
        rw [h6] at h4 
        linarith 
      constructor <;> linarith 
    · -- Backward implication: -1/2 < x ∧ x < 5/2 → |g(x-1)| < 1
      rintro ⟨h1, h2⟩
      have h3 : g (x - 1) < 1 := by
        have h4 : x - 1 < f 1 := by
          rw [h5]
          linarith 
        have h6 : f (g (x - 1)) = x - 1 := by 
          rw [hg2 (x - 1)]
        have hf1 : StrictMono f := by
          intro x y hxy
          rw [hf]
          simp at *
          have h1 : (2 : ℝ) ^ x < (2 : ℝ) ^ y := by 
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy
          have h2 : (2 : ℝ) ^ (-x) > (2 : ℝ) ^ (-y) := by 
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hxy)
          all_goals linarith 
        have h7 : g (x - 1) < 1 := by 
          by_contra h
          push_neg at h
          have h8 : f (g (x - 1)) ≥ f 1 := by 
            have h9 : g (x - 1) ≥ 1 := by linarith 
            have h10 : f (g (x - 1)) ≥ f 1 := hf1.monotone h9 
            linarith 
          linarith [h6, h8, h4] 
        linarith 
      have h4 : g (x - 1) > -1 := by
        have h5 : x - 1 > f (-1) := by
          rw [h6]
          linarith 
        have h7 : f (g (x - 1)) = x - 1 := by 
          rw [hg2 (x - 1)]
        have hf1 : StrictMono f := by
          intro x y hxy
          rw [hf]
          simp at *
          have h1 : (2 : ℝ) ^ x < (2 : ℝ) ^ y := by 
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hxy
          have h2 : (2 : ℝ) ^ (-x) > (2 : ℝ) ^ (-y) := by 
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hxy)
          all_goals linarith 
        have h8 : g (x - 1) > -1 := by 
          by_contra h
          push_neg at h
          have h9 : f (g (x - 1)) ≤ f (-1) := by 
            have h10 : g (x - 1) ≤ -1 := by linarith 
            have h11 : f (g (x - 1)) ≤ f (-1) := hf1.monotone h10 
            linarith 
          linarith [h7, h9, h5] 
        linarith 
      constructor <;> linarith