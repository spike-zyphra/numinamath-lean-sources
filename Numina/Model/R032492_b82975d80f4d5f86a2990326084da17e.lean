import Mathlib

open Real Set
open scoped Real

theorem algebra_116498 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 13 + cos x ^ 14) :
    IsGreatest (range f) 1 := by 
  constructor
  · -- Show 1 is in the range
    use 0 
    rw [hf]
    norm_num 
  · -- Show it is the greatest 
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx 
    simp at hx
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
    have h2 : sin x ^ 13 + cos x ^ 14 ≤ 1 := by 
      have h3 : sin x ^ 2 ≤ 1 := by 
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x)]
      have h4 : cos x ^ 2 ≤ 1 := by 
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x), sq_nonneg (cos x)]
      have h5 : sin x ^ 13 ≤ sin x ^ 2 := by
        have h01 : sin x ^ 2 ≥ 0 := by 
          apply pow_two_nonneg
        by_cases h5 : sin x ≥ 0 
        · -- sin x >= 0
          have h7 : sin x ≤ 1 := by
            nlinarith [sin_le_one x]
          have h8 : sin x ^ 11 ≤ 1 := by 
            have h61 : sin x ≤ 1 := h7
            have h62 : sin x ≥ 0 := h5
            nlinarith [pow_two_nonneg (sin x ^ 5), pow_two_nonneg (sin x ^ 4), pow_two_nonneg (sin x ^ 3), pow_two_nonneg (sin x ^ 2), pow_two_nonneg (sin x), sq_nonneg (sin x - 1), mul_nonneg (show 0 ≤ sin x by linarith) (show 0 ≤ 1 - sin x by nlinarith)]
          nlinarith [pow_two_nonneg (sin x ^ 5), pow_two_nonneg (sin x ^ 4), pow_two_nonneg (sin x ^ 3), pow_two_nonneg (sin x ^ 2), pow_two_nonneg (sin x), sq_nonneg (sin x - 1)]
        · -- sin x < 0 
          have h6 : sin x < 0 := by 
            nlinarith 
          have h70 : sin x ^ 11 < 0 := by 
            have h61 : sin x < 0 := h6 
            have h67 : sin x ^ 11 < 0 := by 
              have h63 : sin x < 0 := h6 
              have h64 : sin x ^ 11 = sin x ^ 10 * sin x := by ring
              rw [h64] 
              have h65 : sin x ^ 10 > 0 := by 
                have h66 : sin x < 0 := h6 
                have h67 : sin x ^ 2 > 0 := by nlinarith 
                have h68 : sin x ^ 10 = (sin x ^ 2) ^ 5 := by ring 
                rw [h68] 
                positivity 
              have h68 : sin x < 0 := h6 
              nlinarith 
            linarith 
          nlinarith [sq_nonneg (sin x ^ 5), sq_nonneg (sin x ^ 4), sq_nonneg (sin x ^ 3), sq_nonneg (sin x ^ 2), sq_nonneg (sin x), sq_nonneg (sin x + 1), h6, sin_le_one x, Real.sin_sq_add_cos_sq x]
      have h6 : cos x ^ 14 ≤ cos x ^ 2 := by
        have h01 : cos x ^ 2 ≥ 0 := by
          apply pow_two_nonneg
        have h02 : cos x ^ 2 ≤ 1 := h4 
        have h73 : cos x ^ 14 ≤ cos x ^ 2 := by 
          have h84 : cos x ^ 14 = (cos x ^ 2) ^ 7 := by ring 
          rw [h84] 
          have h85 : cos x ^ 2 ≤ 1 := h4 
          have h86 : cos x ^ 2 ≥ 0 := by 
            apply pow_two_nonneg 
          have h87 : (cos x ^ 2) ^ 7 ≤ cos x ^ 2 := by 
            have h88 : cos x ^ 2 ≤ 1 := h4 
            have h89 : cos x ^ 2 ≥ 0 := by 
              apply pow_two_nonneg 
            nlinarith [sq_nonneg ((cos x ^ 2) ^ 3), sq_nonneg ((cos x ^ 2) ^ 2), sq_nonneg ((cos x ^ 2) ^ 1), sq_nonneg (cos x ^ 2 - 1), pow_two_nonneg (cos x ^ 2), mul_nonneg (show 0 ≤ 1 - cos x ^ 2 by nlinarith) (show 0 ≤ cos x ^ 2 by nlinarith)]
          nlinarith 
        linarith 
      nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 1), sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x ^ 2 + cos x ^ 2 -1) ]
    linarith [h2]