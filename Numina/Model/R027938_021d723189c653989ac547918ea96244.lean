import Mathlib


open Real


lemma lemma_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 2 * x - Real.sqrt (x * y) - 4 * Real.sqrt (x / y) + 2 = 0) :
    y = 4 * x ∨ x * y = 4 := by
  have h1 : 0 < Real.sqrt (x * y) := by
    positivity
  have h2 : 0 < Real.sqrt (x / y) := by
    positivity
  have h3 : Real.sqrt (x * y) * Real.sqrt (x / y) = x := by
    have h4 : Real.sqrt (x * y) * Real.sqrt (x / y) = Real.sqrt ((x * y) * (x / y)) := by
      rw [← Real.sqrt_mul (by positivity)]
    have h5 : (x * y) * (x / y) = x ^ 2 := by
      field_simp
      <;> nlinarith
    rw [h5] at h4
    rw [h4]
    have h6 : Real.sqrt ((x) ^ 2) = x := by
      rw [Real.sqrt_sq (show 0 ≤ x by linarith)]
    linarith
  have h40 : Real.sqrt (x * y) + 4 * Real.sqrt (x / y) = 2 * x + 2 := by
    nlinarith
  have h6 : (Real.sqrt (x * y) + 4 * Real.sqrt (x / y)) ^ 2 = (2 * x + 2) ^ 2 := by
    rw [h40]
  have h7 : (Real.sqrt (x * y) + 4 * Real.sqrt (x / y)) ^ 2 = (Real.sqrt (x * y)) ^ 2 + 2 * (Real.sqrt (x * y) * (4 * Real.sqrt (x / y))) + (4 * Real.sqrt (x / y)) ^ 2 := by
    ring
  have h8 : (Real.sqrt (x * y)) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    positivity
  have h10 : 2 * (Real.sqrt (x * y) * (4 * Real.sqrt (x / y))) = 8 * x := by
  -- calc
  --   2 * (Real.sqrt (x * y) * (4 * Real.sqrt (x / y))) = 8 * (Real.sqrt (x * y) * Real.sqrt (x / y)) := by ring
  --   _ = 8 * x := by
  --     rw [h3]
    nlinarith [h3]
  have h11 : (4 * Real.sqrt (x / y)) ^ 2 = 16 * (x / y) := by
    calc
      (4 * Real.sqrt (x / y)) ^ 2 = 16 * (Real.sqrt (x / y) ^ 2) := by ring
      _ = 16 * (x / y) := by
        have h80 : Real.sqrt (x / y) ^ 2 = x / y := by
          rw [Real.sq_sqrt]
          positivity
        rw [h80]
  rw [h7] at h6
  rw [h8, h10, h11] at h6
  have h81 : 4 * x ^ 2 * y + 4 * y = x * y ^ 2 + 16 * x := by
  -- Multiply the previous by y
    have h800 : 4 * x ^ 2 + 8 * x + 4 = x * y + 8 * x + 16 * (x / y) := by
      nlinarith
    have h801 : (4 * x ^ 2 + 8 * x + 4) * y = (x * y + 8 * x + 16 * (x / y)) * y := by
      rw [h800]
    have h802 : (4 * x ^ 2 + 8 * x + 4) * y = 4 * x ^ 2 * y + 8 * x * y + 4 * y := by
      ring
    have h803 : (x * y + 8 * x + 16 * (x / y)) * y = x * y ^ 2 + 8 * x * y + 16 * x := by
      field_simp
      ring
    rw [h802, h803] at h801
    nlinarith
  have h82 : (4 * x - y) * (x * y - 4) = 0 := by
    nlinarith [sq_nonneg (4 * x - y), sq_nonneg (x * y - 4), mul_pos hx hy]
  cases' (mul_eq_zero.1 h82) with h83 h84
  ·
    left
    linarith
  ·
    right
    nlinarith


theorem algebra_160382 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : 2 * x - Real.sqrt (x * y) - 4 * Real.sqrt (x / y) + 2 = 0)
    (h2 : 2 * x ^ 2 + x ^ 2 * y ^ 4 = 18 * y ^ 2) :
    (x, y) = (2, 2) ∨ (x, y) = (286 ^ ((1 : ℝ) / 4) / 4, 286 ^ ((1 : ℝ) / 4)) := by


  have h3 : y = 4 * x ∨ x * y = 4 := by
    apply lemma_1 x y hx hy h1


  cases h3 with
  | inl h3 =>
    have hy4 : y = 4 * x := h3
    rw [hy4] at h2
    have h30 : 256 * x ^ 6 - 286 * x ^ 2 = 0 := by
      nlinarith
    have h31 : x ^ 2 * (256 * x ^ 4 - 286) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h31) with h32 h33
    ·
      have h34 : x ^ 2 = 0 := h32
      have h35 : x = 0 := by
        nlinarith
      linarith
    ·
      have h34 : 256 * x ^ 4 = 286 := by
        nlinarith
      have hx21 : x = (286 : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
        have h70 : x ^ 4 = (286 / 256 : ℝ) := by
          nlinarith
        have h71 : x = ((x) ^ 4) ^ ((1 : ℝ) / 4) := by
          rw [show (x ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = x by
            have h10 : (x ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = (x) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals nlinarith
            linarith
          ]
        rw [h70] at h71
        have h72 : ((286 / 256 : ℝ) : ℝ) ^ ((1 : ℝ) / 4) = (286 : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
          have h73 : ((286 / 256 : ℝ) : ℝ) ^ ((1 : ℝ) / 4) = ((286 : ℝ) ^ ((1 : ℝ) / 4)) / ((256 : ℝ) ^ ((1 : ℝ) / 4)) := by
            rw [← Real.div_rpow]
            all_goals
              norm_num
          have h74 : (256 : ℝ) ^ ((1 : ℝ) / 4) = (4 : ℝ) := by
            have h75 : (256 : ℝ) = (4 : ℝ) ^ (4 : ℝ) := by
              norm_num
            rw [h75]
            rw [← Real.rpow_mul]
            norm_num
            all_goals
              norm_num
          rw [h73, h74]
        have h73 : x = (286 : ℝ) ^ ((1 : ℝ) / 4) / 4 := by
          nlinarith [h71, h72]
        linarith
      have hy21 : y = (286 : ℝ) ^ ((1 : ℝ) / 4) := by
        nlinarith [hx21, h3]
      right
      simp [hx21, hy21]
  | inr h3 =>
    have hxy4 : x * y = 4 := h3
    have h40 : 2 * x ^ 2 + x ^ 2 * y ^ 4 = 18 * y ^ 2 := h2
    have h41 : y ^ 4 = 16 := by
      have h42 : x = 4 / y := by
        field_simp
        nlinarith
      rw [h42] at h40
      field_simp at h40
      nlinarith [sq_pos_of_pos hy, sq_nonneg (y ^ 2 - 4), sq_nonneg (y ^ 2)]
    have hy2 : y = 2 := by
      have h43 : y ^ 4 - 16 = 0 := by
        nlinarith
      have h44 : y ^ 4 - 16 = (y ^ 2 - 4) * (y ^ 2 + 4) := by ring
      rw [h44] at h43
      cases' (mul_eq_zero.1 h43) with h45 h46
      ·
        have h47 : y ^ 2 = 4 := by
          nlinarith
        have hy2 : y = 2 := by
          nlinarith
        exact hy2
      ·
        have h47 : y ^ 2 + 4 > 0 := by
          nlinarith [sq_nonneg y]
        nlinarith
    have hx2 : x = 2 := by
      nlinarith [hxy4, hy2]
    left
    simp [hx2, hy2]