import Mathlib

theorem algebra_184955 : 2 * Real.sqrt (40 * Real.sqrt 12) + 3 * Real.sqrt (5 * Real.sqrt 48) - 2 * 75 ^ ((1 : ℝ) / 4) - 4 * Real.sqrt (15 * Real.sqrt 27) = 0 := by
  have h1 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h4 : (40 * Real.sqrt 12) = 80 * Real.sqrt 3 := by
    rw [h1]
    all_goals linarith
  have h5 : Real.sqrt (40 * Real.sqrt 12) = Real.sqrt (80 * Real.sqrt 3) := by
    rw [show (40 * Real.sqrt 12) = 80 * Real.sqrt 3 by linarith [h4]]
  have h6 : (5 * Real.sqrt 48) = 20 * Real.sqrt 3 := by
    rw [h2]
    all_goals linarith
  have h7 : Real.sqrt (5 * Real.sqrt 48) = Real.sqrt (20 * Real.sqrt 3) := by
    rw [show (5 * Real.sqrt 48) = 20 * Real.sqrt 3 by linarith [h6]]
  have h8 : (15 * Real.sqrt 27) = 45 * Real.sqrt 3 := by
    rw [h3]
    all_goals linarith
  have h9 : Real.sqrt (15 * Real.sqrt 27) = Real.sqrt (45 * Real.sqrt 3) := by
    rw [show (15 * Real.sqrt 27) = 45 * Real.sqrt 3 by linarith [h8]]
  have h10 : Real.sqrt (80 * Real.sqrt 3) = 4 * (75 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h101 : Real.sqrt (80 * Real.sqrt 3) = Real.sqrt (4 ^ 2 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
      have h : (80 * Real.sqrt 3 : ℝ) = (4 ^ 2 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
        have h2 : (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) := by
          rw [show (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) by simp [Real.sqrt_eq_rpow]]
        rw [h2]
        have h3 : Real.sqrt (75 : ℝ) = 5 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h3]
        all_goals nlinarith [Real.sqrt_nonneg (75 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
      rw [h]
    rw [h101]
    have h102 : Real.sqrt (4 ^ 2 * (75 : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (4 ^ 2) * Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h102]
    have h103 : Real.sqrt ((4 : ℝ) ^ 2) = (4 : ℝ) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [h103]
    have h104 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = (75 : ℝ) ^ ((1 / 4 : ℝ)) := by
      have h105 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [show ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) by simp [Real.sqrt_eq_rpow]]
      rw [h105]
      have h106 : ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = (75 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals positivity
      rw [h106]
    rw [h104]
    all_goals norm_num
  have h11 : Real.sqrt (20 * Real.sqrt 3) = 2 * (75 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h111 : Real.sqrt (20 * Real.sqrt 3) = Real.sqrt (4 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
      have h : (20 * Real.sqrt 3 : ℝ) = (4 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
        have h2 : (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) := by
          rw [show (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) by simp [Real.sqrt_eq_rpow]]
        rw [h2]
        have h3 : Real.sqrt (75 : ℝ) = 5 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h3]
        all_goals nlinarith [Real.sqrt_nonneg (75 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
      rw [h]
    rw [h111]
    have h112 : Real.sqrt (4 * (75 : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (4) * Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h112]
    have h113 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h113]
    have h114 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = (75 : ℝ) ^ ((1 / 4 : ℝ)) := by
      have h105 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [show ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) by simp [Real.sqrt_eq_rpow]]
      rw [h105]
      have h106 : ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = (75 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals positivity
      rw [h106]
    rw [h114]
    all_goals norm_num
  have h12 : Real.sqrt (45 * Real.sqrt 3) = 3 * (75 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h121 : Real.sqrt (45 * Real.sqrt 3) = Real.sqrt (9 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
      have h : (45 * Real.sqrt 3 : ℝ) = (9 * (75 : ℝ) ^ (1 / 2 : ℝ)) := by
        have h2 : (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) := by
          rw [show (75 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (75 : ℝ) by simp [Real.sqrt_eq_rpow]]
        rw [h2]
        have h3 : Real.sqrt (75 : ℝ) = 5 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h3]
        all_goals nlinarith [Real.sqrt_nonneg (75 : ℝ), Real.sqrt_nonneg (3 : ℝ)]
      rw [h]
    rw [h121]
    have h122 : Real.sqrt (9 * (75 : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (9) * Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h122]
    have h123 : Real.sqrt (9 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h123]
    have h124 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = (75 : ℝ) ^ ((1 / 4 : ℝ)) := by
      have h105 : Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) = ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [show ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt ((75 : ℝ) ^ (1 / 2 : ℝ)) by simp [Real.sqrt_eq_rpow]]
      rw [h105]
      have h106 : ((75 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = (75 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals positivity
      rw [h106]
    rw [h124]
    all_goals norm_num
  rw [h5, h10, h7, h11, h9, h12]
  all_goals ring_nf
  all_goals norm_num
  <;> ring
  <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring
  all_goals try { norm_num }
  all_goals try { ring_nf }
  all_goals try { norm_num }
  all_goals try { ring }