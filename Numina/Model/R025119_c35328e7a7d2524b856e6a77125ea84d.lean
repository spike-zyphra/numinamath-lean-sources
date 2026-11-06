import Mathlib

theorem algebra_200748 (x : ℝ) (hx : 0 < x) (h : x * 3^x = 3^18) (k : ℕ) (hk : 0 < k)
    (hk1 : k < x) (hk2 : x < k + 1) : k = 15 := by

  have h1 : (15 : ℝ) < x := by
    by_contra h2
    push_neg at h2
    have h3 : x ≤ (15 : ℝ) := by linarith
    have h4 : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (15 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals
        norm_num
      all_goals
        linarith
    have h5 : x * ((3 : ℝ) ^ x) ≤ (15 : ℝ) * ((3 : ℝ) ^ (15 : ℝ)) := by
      have h6 : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ (15 : ℝ) := h4
      have h7 : x ≤ (15 : ℝ) := h3
      have h8 : (3 : ℝ) ^ (15 : ℝ) ≥ 0 := by positivity
      nlinarith [h6, show (3 : ℝ) ^ (15 : ℝ) ≥ 0 by positivity]
    have h8 : (15 : ℝ) * ((3 : ℝ) ^ (15 : ℝ)) < (3 : ℝ) ^ (18 : ℝ) := by
      have h11 : (3 : ℝ) ^ (15 : ℝ) > 0 := by positivity
      have h12 : (3 : ℝ) ^ (18 : ℝ) = (3 : ℝ) ^ (15 : ℝ) * ((3 : ℝ) ^ (3 : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals
          norm_num
      have h13 : (3 : ℝ) ^ (3 : ℝ) = (27 : ℝ) := by
        norm_num
      rw [h13] at h12
      nlinarith [show (3 : ℝ) ^ (15 : ℝ) > 0 by positivity]
    have h15 : x * ((3 : ℝ) ^ x) < (3 : ℝ) ^ (18 : ℝ) := by
      linarith
    nlinarith [h, h15]

  have h2 : x < (16 : ℝ) := by
    by_contra h3
    push_neg at h3
    have h4 : x ≥ (16 : ℝ) := by linarith
    have h5 : (3 : ℝ) ^ x ≥ (3 : ℝ) ^ (16 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals
        norm_num
      all_goals
        linarith
    have h6 : x * ((3 : ℝ) ^ x) ≥ (16 : ℝ) * ((3 : ℝ) ^ (16 : ℝ)) := by
      have h7 : (3 : ℝ) ^ x ≥ (3 : ℝ) ^ (16 : ℝ) := h5
      have h8 : x ≥ (16 : ℝ) := h4
      have h9 : (3 : ℝ) ^ (16 : ℝ) ≥ 0 := by positivity
      nlinarith [h7, h9]
    have h10 : (16 : ℝ) * ((3 : ℝ) ^ (16 : ℝ)) > (3 : ℝ) ^ (18 : ℝ) := by
      have h11 : (3 : ℝ) ^ (16 : ℝ) > 0 := by positivity
      have h12 : (3 : ℝ) ^ (18 : ℝ) = (3 : ℝ) ^ (16 : ℝ) * ((3 : ℝ) ^ (2 : ℝ)) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals
          norm_num
      have h13 : (3 : ℝ) ^ (2 : ℝ) = (9 : ℝ) := by
        norm_num
      rw [h13] at h12
      nlinarith [show (3 : ℝ) ^ (16 : ℝ) > 0 by positivity]
    have h14 : x * ((3 : ℝ) ^ x) > (3 : ℝ) ^ (18 : ℝ) := by
      linarith
    nlinarith [h, h14]

  have hk3 : k ≥ 15 := by
    by_contra h3
    push_neg at h3
    have hk4 : k ≤ 14 := by
      omega
    have hk5 : (k : ℝ) ≤ (14 : ℝ) := by exact_mod_cast hk4
    have h10 : (k : ℝ) < (15 : ℝ) := by
      nlinarith
    nlinarith [show (k : ℝ) < (15 : ℝ) from by nlinarith, h1]

  have hk4 : k ≤ 15 := by
    by_contra h3
    push_neg at h3
    have hk5 : k ≥ 16 := by
      omega
    have hk6 : (k : ℝ) ≥ (16 : ℝ) := by exact_mod_cast hk5
    nlinarith [show (k + 1 : ℝ) ≥ (16 : ℝ) from by nlinarith, h2, hk6]

  have hk8 : k = 15 := by
    omega
  exact hk8