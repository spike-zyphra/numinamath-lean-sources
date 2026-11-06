import Mathlib

open Real Set

theorem inequalities_144416 {x : ℝ} (hx : 0 ≤ x) :
    (sqrt x - 2) / (1 - sqrt (x + 1)) ≥ 1 + sqrt (x + 1) ↔ x ∈ Ioc 0 1 := by
  constructor
  · -- Assume the inequality $\frac{\sqrt{x}-2}{1-\sqrt{x+1}} \geq 1+\sqrt{x+1}$ holds, prove $x \in (0, 1]$.
    intro h
    by_cases h1 : x > 0
    · -- Assume that x > 0
      have h2 : sqrt x ≥ 0 := Real.sqrt_nonneg x
      have h3 : sqrt (x + 1) ≥ 1 := by
        have h31 : sqrt (x + 1) ≥ sqrt (1 : ℝ) := by
          apply Real.sqrt_le_sqrt
          linarith
        have h32 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
        nlinarith
      have h4 : 1 - sqrt (x + 1) < 0 := by
        have h5 : sqrt (x + 1) > 1 := by
          have h6 : x + 1 > (1 : ℝ) := by
            nlinarith
          have h7 : sqrt (x + 1) > sqrt (1 : ℝ) := by
            apply Real.sqrt_lt_sqrt
            all_goals nlinarith
          have h8 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
          nlinarith
        linarith
      have h6 : (sqrt x - 2) / (1 - sqrt (x + 1)) ≥ 1 + sqrt (x + 1) := h
      have h7 : sqrt x - 2 ≤ (1 + sqrt (x + 1)) * (1 - sqrt (x + 1)) := by
        have h7 : (sqrt x - 2) / (1 - sqrt (x + 1)) ≥ 1 + sqrt (x + 1) := h
        have h8_neg : (1 - sqrt (x + 1)) < 0 := h4
        have h7' : sqrt x - 2 ≤ (1 + sqrt (x + 1)) * (1 - sqrt (x + 1)) := by
          by_contra h
          push_neg at h
          -- We have sqrt x - 2 > (1 + sqrt (x + 1)) * (1 - sqrt (x + 1))
          -- we show it contradicts h: (sqrt x - 2) / (1 - sqrt (x + 1)) ≥ 1 + sqrt (x + 1)
          have h12 : (sqrt x - 2) / (1 - sqrt (x + 1)) < 1 + sqrt (x + 1) := by
            have h8_neg : (1 - sqrt (x + 1)) < 0 := h4
            apply (div_lt_iff_of_neg' (by linarith)).mpr
            linarith
          linarith -- contradicts h and h12
        exact h7'
      have h9 : (1 + sqrt (x + 1)) * (1 - sqrt (x + 1)) = -x := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith)]
      rw [h9] at h7
      constructor
      · -- Show 0 < x
        linarith
      · -- Show x ≤ 1
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith), sq_nonneg (sqrt x - 1), sq_nonneg (x - 1)]
    · -- Assume x ≤ 0
      have : x = 0 := by linarith
      rw [this] at h
      norm_num [Real.sqrt_eq_iff_sq_eq] at h
  · -- Assume x ∈ (0; 1], need to prove the inequality.
    rintro ⟨hx1, hx2⟩
    have h12 : sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h121 : sqrt (x + 1) ≥ 1 := by
      have h31 : sqrt (x + 1) ≥ sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h32 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      nlinarith
    have h122 : sqrt x ≤ 1 := by
      have h21 : sqrt x ≤ sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h22 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      nlinarith
    have h4 : 1 - sqrt (x + 1) < 0 := by
      have h51 : sqrt (x + 1) > 1 := by
        have h52 : x + 1 > (1 : ℝ) := by
          nlinarith
        have h54 : sqrt (x + 1) > sqrt (1 : ℝ) := by
          apply Real.sqrt_lt_sqrt
          all_goals nlinarith
        have h55 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
        nlinarith
      linarith
    have h5 : sqrt x - 2 ≤ (1 + sqrt (x + 1)) * (1 - sqrt (x + 1)) := by
      have h124 : (1 + sqrt (x + 1)) * (1 - sqrt (x + 1)) = -x := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)]
      rw [h124]
      have h125 : sqrt x ≥ 0 := by apply Real.sqrt_nonneg
      have h126 : sqrt x ≤ 1 := h122
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), sq_nonneg (sqrt x - 1)]
    have h6 : (sqrt x - 2) / (1 - sqrt (x + 1)) ≥ 1 + sqrt (x + 1) := by
      have h7 : 1 - sqrt (x + 1) < 0 := h4
      apply (le_div_iff_of_neg' (by linarith)).mpr
      linarith
    exact h6