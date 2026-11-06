import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_83536 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 1 / x - 4 / sqrt x + 3) :
  f '' Icc (1 / 16) 1 = Icc (-1) 3 := by
  ext y
  simp only [mem_image, mem_setOf_eq, mem_Icc]
  constructor
  · -- Assume y ∈ f '' Icc (1 / 16) 1, prove y ∈ Icc (-1) 3
    rintro ⟨x, hx, hfx⟩
    have hx1 : 1 / 16 ≤ x := by
      have h : x ∈ Icc (1 / 16) 1 := by
        simpa using hx
      exact h.1
    have hx2 : x ≤ 1 := by
      have h : x ∈ Icc (1 / 16) 1 := by
        simpa using hx
      exact h.2
    have h1 : 0 < x := by
      linarith
    have h2 : 0 < sqrt x := by
      apply Real.sqrt_pos.2
      linarith
    have h3 : sqrt x ≥ 1 / 4 := by
      have h4 : sqrt x ≥ Real.sqrt (1 / 16 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h5 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      nlinarith [h5]
    have h3a : sqrt x ≤ 1 := by
      have h4 : sqrt x ≤ Real.sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      have h5 : Real.sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_one]
      nlinarith [h5]
    have hfx2 : y = 1 / x - 4 / sqrt x + 3 := by
      rw [h₀ x] at hfx
      linarith
    have h8 : -1 ≤ y := by
      rw [hfx2]
      have h10 : (sqrt x) > 0 := by positivity
      have h11 : 1 / x - 4 / sqrt x + 3 ≥ -1 := by
        have h12 : (sqrt x) > 0 := by positivity
        have h13 : 1 / x - 4 / sqrt x + 3 + 1 ≥ 0 := by
          have h14 : 1 / x - 4 / sqrt x + 3 + 1 = (1 - 4 * (sqrt x) + 4 * (sqrt x)^2) / ((sqrt x)^2) := by 
            have h15 : sqrt x > 0 := by positivity
            field_simp [h15]
            <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
          rw [h14]
          have h16 : 0 < (sqrt x)^2 := by
            have h17 : sqrt x > 0 := by positivity
            nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
          have h17 : (1 - 4 * (sqrt x) + 4 * (sqrt x)^2) ≥ 0 := by
            nlinarith [sq_nonneg (2 * sqrt x - 1), Real.sq_sqrt (show 0 ≤ x by linarith)]
          apply div_nonneg
          · linarith
          · nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]
        linarith
      linarith
    have h8a : y ≤ 3 := by
      rw [hfx2]
      have h10 : (sqrt x) > 0 := by positivity
      have h11 : 1 / x - 4 / sqrt x + 3 ≤ 3 := by
        have h12 : (sqrt x) > 0 := by positivity
        have h13 : 1 / x - 4 / sqrt x ≤ 0 := by
          have h14 : 1 / x - 4 / sqrt x = (sqrt x - 4 * x) / (x * sqrt x) := by
            field_simp [show sqrt x > 0 by positivity, show x > 0 by linarith]
            <;> nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith)]
          rw [h14]
          have h15 : sqrt x > 0 := by positivity
          have h16 : x > 0 := by linarith
          have h17 : (sqrt x - 4 * x) / (x * sqrt x) ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg
            · -- Show sqrt x - 4 * x ≤ 0
              nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), sq_nonneg (sqrt x - 1 / 4), Real.sqrt_nonneg x, sq_nonneg (sqrt x - 1 / 4)]
            · -- Show x * sqrt x ≥ 0
              positivity
          linarith
        linarith
      linarith
    constructor
    · linarith
    · linarith
  · -- Assume y ∈ Icc (-1) 3, prove y ∈ f '' Icc (1 / 16) 1
    rintro ⟨hy1, hy2⟩
    by_cases h6 : y = 3
    · -- y = 3
      use (1 / 16 : ℝ)
      constructor
      · -- Show 1/16 ∈ Icc (1/16) 1
        norm_num
      · -- Show f (1/16) = 3
        rw [h₀]
        rw [h6]
        have h24 : sqrt ((1 / 16 : ℝ)) = 1 / 4 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        rw [h24]
        norm_num
    · -- y < 3
      have h7 : y < 3 := by
        by_contra h
        push_neg at h
        have h8 : y ≥ 3 := by linarith
        have h9 : y ≤ 3 := by linarith
        have h10 : y = 3 := by linarith
        tauto
      have h4 : (3 - y : ℝ) > 0 := by linarith
      have h35 : ∃ t : ℝ, (3 - y) * t ^ 2 - 4 * t + 1 = 0 ∧ (1 / 4 ≤ t ∧ t ≤ 1) := by
        use (2 - Real.sqrt (1 + y) ) / (3 - y)
        constructor
        · -- Show it's a root
          field_simp [show (3 - y) ≠ 0 by linarith]
          nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + y) by nlinarith)]
        · -- Show t ∈ [1/4, 1]
          constructor
          · -- Show t ≥ 1/4
            have h14 : (2 - Real.sqrt (1 + y) ) / (3 - y) ≥ 1 / 4 := by
              apply (le_div_iff₀ (by linarith)).mpr
              nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + y) by nlinarith), sq_nonneg (y - 3)]
            linarith
          · -- Show t ≤ 1
            have h15 : (2 - Real.sqrt (1 + y) ) / (3 - y) ≤ 1 := by
              apply (div_le_iff₀ (by linarith)).mpr
              nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + y) by nlinarith)]
            linarith
      rcases h35 with  ⟨t, ht_eq, ht14, ht1⟩
      use t^2
      constructor
      · -- Show t^2 ∈ Icc (1 / 16) 1
        constructor
        · -- Show t^2 ≥ 1/16
          nlinarith [sq_nonneg (t - 1 / 4), sq_nonneg (t - 1), ht14, ht1]
        · -- Show t^2 ≤ 1
          nlinarith [sq_nonneg (t - 1 / 4), sq_nonneg (t - 1), ht14, ht1]
      · -- Show f (t^2) = y
        have h13 : 0 < t := by
          nlinarith
        have h14 : sqrt (t^2) = t := by
          rw [Real.sqrt_sq]
          positivity
        have h15 : y = 1 / (t^2) - 4 / t + 3 := by
          have h16 : (3 - y : ℝ) * t ^ 2 - 4 * t + 1 = 0 := ht_eq
          have h17 : t > 0 := by
            nlinarith
          field_simp [show t ≠ 0 by nlinarith] at h16 ⊢
          nlinarith [sq_pos_of_pos (show t > 0 by nlinarith)]
        have h18 : f (t^2) = 1 / (t^2) - 4 / t + 3 := by
          rw [h₀]
          have h19 : sqrt (t^2) = t := h14
          simp [h19]
        linarith [h15, h18]