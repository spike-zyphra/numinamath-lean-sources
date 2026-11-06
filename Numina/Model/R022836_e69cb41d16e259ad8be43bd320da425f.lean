import Mathlib


open Real Set


lemma lemma_1 (a b c d : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) ≥
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) := by
  have h1 : (Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 ≥
      (Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2)) ^ 2 := by
    have h2 : (Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 =
        (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 + (Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 + 2 * (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) := by ring
    rw [h2]
    have h3 : (Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2)) ^ 2 = (a + c) ^ 2 + (b + d) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
    rw [h3]
    have h4 : (Real.sqrt (a ^ 2 + b ^ 2 : ℝ) ) ^ 2 = a ^2 + b ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h5 : (Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ) ^ 2 = c ^ 2 + d ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h4, h5]
    have h7 : Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) ≥ a * c + b * d := by
      have h8 : (Real.sqrt (a ^ 2 + b ^ 2 : ℝ) * Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ) ^ 2 ≥ (a * c + b * d) ^ 2 := by
        have h9 : (Real.sqrt (a ^ 2 + b ^ 2 : ℝ) * Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ) ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2 : ℝ) ) ^ 2 * (Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ) ^ 2 := by ring
        rw [h9]
        have h10 : (Real.sqrt (a ^ 2 + b ^ 2 : ℝ) ) ^ 2 = a ^ 2 + b ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        have h11 : (Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ) ^ 2 = c ^ 2 + d ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h10, h11]
        nlinarith [sq_nonneg (a * d - b * c)]
      have h6 : Real.sqrt (a ^ 2 + b ^ 2 : ℝ) * Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ≥ 0 := by positivity
      have h13 : (a * c + b * d) ≤ Real.sqrt (a ^ 2 + b ^ 2 : ℝ) * Real.sqrt (c ^ 2 + d ^ 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2 : ℝ), Real.sqrt_nonneg (c ^ 2 + d ^ 2 : ℝ), sq_nonneg (a * d - b * c), Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (c ^ 2 + d ^ 2 : ℝ) by positivity)]
      linarith
    nlinarith [Real.sqrt_nonneg (a  ^ 2 + b ^ 2 : ℝ), Real.sqrt_nonneg (c ^ 2 + d ^ 2 : ℝ), sq_nonneg (a * d - b * c), Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (c ^ 2 + d ^ 2 : ℝ) by positivity), Real.sqrt_nonneg ((a + c) ^ 2 + (b + d) ^ 2 : ℝ), sq_nonneg (a + c), sq_nonneg (b + d), sq_nonneg (a * d - b * c)]
  have h8 : Real.sqrt (a ^ 2 + b ^ 2 : ℝ) + Real.sqrt (c ^ 2 + d ^ 2 : ℝ) ≥ 0 := by positivity
  have h9 : Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2 : ℝ) ≥ 0 := by positivity
  nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2 : ℝ), Real.sqrt_nonneg (c ^ 2 + d ^ 2 : ℝ), Real.sqrt_nonneg ((a + c) ^ 2 + (b + d) ^ 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ ( (a + c) ^ 2 + (b + d) ^ 2 : ℝ) by positivity ), Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2 : ℝ) by positivity ), Real.sq_sqrt (show (0 : ℝ) ≤ (c ^ 2 + d ^ 2 : ℝ) by positivity )]

theorem algebra_13407 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + (1 - t)^2) + sqrt ((1 - t)^2 + (1 + t)^2)} (sqrt 5) := by
  constructor
  · -- Show that sqrt(5) is in the set
    use 1 / 3
    have h1 : sqrt ( (1 / 3: ℝ) ^ 2 + (1 - (1 / 3: ℝ) )^2 ) + sqrt ( (1 - (1 / 3: ℝ) )^2 + (1 + (1 / 3: ℝ) )^2 ) = sqrt 5 := by
      have h2 : sqrt ( (1 / 3: ℝ) ^ 2 + (1 - (1 / 3: ℝ) )^2 ) = sqrt 5 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h3 : sqrt ( (1 - (1 / 3: ℝ) )^2 + (1 + (1 / 3: ℝ) )^2 ) = 2 * sqrt 5 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h2, h3]
      ring_nf
      <;> norm_num
    linarith [h1]
  · -- Show that sqrt(5) is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h2 : sqrt (t^2 + (1 - t)^2) + sqrt ((1 - t)^2 + (1 + t)^2) ≥ sqrt 5 := by
      have h3 : sqrt (t ^ 2 + (1 - t) ^ 2) + sqrt ((1 - t) ^ 2 + (1 + t) ^ 2) ≥ Real.sqrt ((t + (1 - t)) ^ 2 + ((1 - t) + (1 + t)) ^ 2) := by
        apply lemma_1
        all_goals nlinarith
      have h4 : Real.sqrt ((t + (1 - t)) ^ 2 + ((1 - t) + (1 + t)) ^ 2) = Real.sqrt 5 := by
        have h5 : (t + (1 - t) : ℝ) = 1 := by nlinarith
        have h6 : ((1 - t) + (1 + t) : ℝ) = 2 := by nlinarith
        rw [h5, h6]
        all_goals norm_num
        <;> nlinarith
      rw [h4] at h3
      linarith
    have h3 : x = sqrt (t^2 + (1 - t)^2 ) + sqrt ( (1 - t)^2 + (1 + t)^2 ) := by
      linarith [ht]
    linarith [h3, h2]