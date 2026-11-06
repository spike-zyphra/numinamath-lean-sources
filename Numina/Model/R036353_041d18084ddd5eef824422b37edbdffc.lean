import Mathlib

theorem algebra_5040 {x : ℝ} (hx : x^3 = 2022 + (x - ⌊x⌋)^3) :
    x = 6 + Real.sqrt 1590 / 6 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h7 : x - (⌊x⌋ : ℝ) ≥ 0 := by linarith
  have h8 : x - (⌊x⌋ : ℝ) < 1 := by linarith
  have h9 : ⌊x⌋ = 12 := by
    have h10 : ⌊x⌋ ≤ 12 := by
      by_contra h
      push_neg at h
      have h11 : ⌊x⌋ ≥ 13 := by omega
      have h12 : (⌊x⌋ : ℝ) ≥ 13 := by exact_mod_cast h11
      have h13 : x ≥ 13 := by linarith [h12, h1]
      have h14 : x^3 ≥ 2197 := by
        nlinarith [sq_nonneg (x - 13 : ℝ), sq_nonneg (x ^ 2 - 169 : ℝ), sq_nonneg (x ^ 2 - 13 * x), sq_nonneg (x - 13 : ℝ)]
      have h17 : (x - (⌊x⌋ : ℝ)) ^ 3 < 1 := by
        have h18 : x - (⌊x⌋ : ℝ) < 1 := h8
        have h19 : (x - (⌊x⌋ : ℝ)) ^ 3 < 1 := by
          nlinarith [sq_nonneg (x - (⌊x⌋ : ℝ) - 1 : ℝ), sq_nonneg ((x - (⌊x⌋ : ℝ)) ^ 2 - 1 : ℝ), sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((x - (⌊x⌋ : ℝ)) ^ 2)]
        linarith
      have h18 : x^3 ≤ 2023 := by
        have h19 : (x - (⌊x⌋ : ℝ)) ^ 3 < 1 := h17
        have h20 : (x - (⌊x⌋ : ℝ)) ^ 3 ≥ 0 := by
          have h16 : x - (⌊x⌋ : ℝ) ≥ 0 := by linarith
          nlinarith [sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((x - (⌊x⌋ : ℝ)) ^ 2)]
        have h21 : (x^3) = 2022 + (x - ⌊x⌋)^3 := hx
        nlinarith
      nlinarith
    have h13 : ⌊x⌋ ≥ 12 := by
      by_contra h
      push_neg at h
      have h11 : ⌊x⌋ ≤ 11 := by omega
      have h12 : (⌊x⌋ : ℝ) ≤ 11 := by exact_mod_cast h11
      have h13 : x < 12 := by linarith [h12, h2]
      have h14 : x^3 < 1728 := by
        nlinarith [sq_nonneg (x - 12 : ℝ), sq_nonneg (x ^ 2 - 144 : ℝ), sq_nonneg (x ^ 2 - 12 * x), sq_nonneg (x - 12 : ℝ)]
      have h17 : (x^3) = 2022 + (x - ⌊x⌋)^3 := hx
      have h15 : (x - (⌊x⌋ : ℝ)) ^ 3 ≥ 0 := by
        have h16 : x - (⌊x⌋ : ℝ) ≥ 0 := by linarith
        nlinarith [sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((x - (⌊x⌋ : ℝ)) ^ 2)]
      nlinarith
    omega
  have h18 : (⌊x⌋ : ℝ) = 12 := by exact_mod_cast h9
  have h21 : x^3 = 2022 + (x - (⌊x⌋ : ℝ))^3 := by linarith [hx]
  rw [show (⌊x⌋ : ℝ) = 12 by linarith] at h21
  have h22 : x^3 = 2022 + (x - 12)^3 := by
    nlinarith
  have h24 : (x - 6 : ℝ) ^ 2 = (1590 : ℝ) / 36 := by
    nlinarith [sq_nonneg (x - 12 : ℝ), sq_nonneg (x - 6 : ℝ)]
  have h25 : x - 6 = Real.sqrt 1590 / 6 := by
    have h26 : x ≥ 12 := by
      nlinarith [h18]
    have h27 : (x - 6 : ℝ) ≥ 0 := by linarith
    have h29 : Real.sqrt ((1590 : ℝ) / 36) = Real.sqrt 1590 / 6 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h31 : (x - 6 : ℝ) ^ 2 = (1590 : ℝ) / 36 := h24
    have h32 : (x - 6 : ℝ) = Real.sqrt ((1590 : ℝ) / 36) := by
      have h33 : Real.sqrt ((x - 6 : ℝ) ^ 2) = Real.sqrt ((1590 : ℝ) / 36) := by
        rw [h31]
      have h34 : Real.sqrt ((x - 6 : ℝ) ^ 2) = (x - 6 : ℝ) := by
        apply Real.sqrt_sq
        linarith
      linarith
    rw [h32, h29]
  linarith