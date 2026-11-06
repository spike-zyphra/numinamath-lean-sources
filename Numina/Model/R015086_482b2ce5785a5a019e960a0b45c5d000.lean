import Mathlib

open Real

theorem algebra_167195 {x : ℝ} (hx : x > 0) :
    3 ^ (∑ i ∈ Finset.range 8, logb 3 (x ^ (i + 1))) = 27 * x ^ 30 ↔ x = sqrt 3 := by
  constructor
  · -- Assume the left side, prove the right side.
    intro h_eq
    have h1 : ∑ i in Finset.range 8, logb 3 (x ^ (i + 1)) = 36 * logb 3 x := by
      simp [Finset.sum_range_succ, logb_pow]
      all_goals ring_nf
    rw [h1] at h_eq
    have h2 : (3 : ℝ) ^ (36 * logb 3 x) = x ^ 36 := by
      have h3 : (3 : ℝ) ^ (36 * logb 3 x) = ((3 : ℝ) ^ (logb 3 x)) ^ 36 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals
          try linarith
      have h4 : (3 : ℝ) ^ (logb 3 x) = x := by
        rw [Real.rpow_logb]
        all_goals
          try linarith
      rw [h3, h4]
    rw [h2] at h_eq
    have h3 : x ^ 36 = 27 * x ^ 30 := by
      linarith
    have h4 : x ^ 6 = 27 := by
      have h5 : x ^ 36 = 27 * x ^ 30 := h3
      have h6 : x ^ 36 = x ^ 30 * x ^ 6 := by
        ring_nf
      rw [h6] at h5
      have h7 : x ^ 30 > 0 := by positivity
      have h8 : x ^ 6 = 27 := by
        apply (mul_left_inj' (ne_of_gt h7)).mp
        linarith
      linarith
    have h5 : x ^ 6 = 27 := h4
    have h6 : x ^ 2 = (3 : ℝ) := by
      have h8 : x ^ 6 = (3 : ℝ) ^ 3 := by
        linarith
      have h9 : x ^ 6 = (x ^ 2) ^ 3 := by
        ring
      rw [h9] at h8
      have h10 : (x ^ 2) ^ 3 = (3 : ℝ) ^ 3 := by
        linarith
      have h11 : x ^ 2 ≥ 0 := by positivity
      have h12 : x ^ 2 = (3 : ℝ) := by
        have h8 : (x ^ 2) ^ 3 = (3 : ℝ) ^ 3 := h10
        have h13 : x ^ 2 ≥ 0 := by positivity
        have h14 : (3 : ℝ) ≥ 0 := by norm_num
        have h15 : x ^ 2 = (3 : ℝ) := by
          have h19 : (x ^ 2) ^ 3 - (3 : ℝ) ^ 3 = 0 := by linarith
          have h19 : (x ^ 2 - (3 : ℝ)) * ((x ^ 2) ^ 2 + (x ^ 2) * (3 : ℝ) + (3 : ℝ) ^ 2) = 0 := by
            nlinarith
          cases' (mul_eq_zero.1 h19) with h20 h21
          · -- case $x^2 - 3 = 0$
            nlinarith
          · -- case $(x^2)^2 + x^2 \cdot 3 + 3^2 = 0$
            nlinarith [sq_nonneg ((x ^ 2) ^ 2), sq_nonneg (x ^ 2 * (3 : ℝ)), sq_nonneg ((3 : ℝ) ^ 2)]
        linarith
      linarith
    have h10 : x = Real.sqrt (3 : ℝ) := by
      have h11 : x ^ 2 = 3 := by
        linarith
      have h12 : x > 0 := hx
      have h13 : x = Real.sqrt (3 : ℝ) := by
        rw [← h11]
        field_simp
      exact h13
    linarith
  · -- Assume x = sqrt 3, prove the left side.
    intro h_eq
    rw [h_eq]
    have h1 : ∑ i in Finset.range 8, logb 3 ((sqrt 3) ^ (i + 1)) = 36 * logb 3 (sqrt 3) := by
      simp [Finset.sum_range_succ, logb_pow]
      all_goals ring_nf
    rw [h1]
    have h2 : (3 : ℝ) ^ (36 * logb 3 (sqrt 3)) = (sqrt 3) ^ 36 := by
      have h3 : (3 : ℝ) ^ (36 * logb 3 (sqrt 3)) = ((3 : ℝ) ^ (logb 3 (sqrt 3)) ) ^ 36 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals
          try linarith [Real.sqrt_nonneg (3 : ℝ)]
      have h4 : (3 : ℝ) ^ (logb 3 (sqrt 3)) = (sqrt 3 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals
          try linarith [Real.sqrt_nonneg (3 : ℝ)]
          try norm_num
      rw [h3, h4]
    rw [h2]
    have h32 : (sqrt 3 : ℝ) ^ 36 = 27 * (sqrt 3) ^ 30 := by
      have h35 : (sqrt 3 : ℝ) ^ 6 = (27 : ℝ) := by
        calc
          (sqrt 3 : ℝ) ^ 6 = ((sqrt 3 : ℝ) ^ 2) ^ 3 := by ring
          _ = (3 : ℝ) ^ 3 := by
            rw [Real.sq_sqrt]
            all_goals
              norm_num
          _ = (27 : ℝ) := by norm_num
      calc
        (sqrt 3 : ℝ) ^ 36 = (sqrt 3 : ℝ) ^ 30 * (sqrt 3 : ℝ) ^ 6 := by ring
        _ = (sqrt 3 : ℝ) ^ 30 * (27 : ℝ) := by rw [h35]
        _ = (27 : ℝ) * (sqrt 3 : ℝ) ^ 30 := by ring
        _ = 27 * (sqrt 3 : ℝ) ^ 30 := by ring
    linarith