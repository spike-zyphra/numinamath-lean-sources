import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_240627 (f : ℝ → ℝ)
  (hf : f = λ x => sqrt (7 * x - 3) / x) :
  IsLeast {y | ∃ x ∈ Icc (1 / 2) 3, f x = y} (sqrt 2) := by
  constructor
  · -- Show that √2 is in the range of f over [1/2, 3]
    use 1 / 2
    constructor
    · -- Show that 1/2 ∈ [1/2, 3]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f(1/2) = √2
      have hfx1 : f (1 / 2) = sqrt 2 := by
        rw [hf]
        -- expand sqrt (7 * (1/2) - 3) / (1/2)
        have h1 : 7 * (1/2 : ℝ) - 3 = (1/2 : ℝ) := by norm_num 
        have h2 : sqrt (7 * (1/2 : ℝ) - 3) = sqrt (1/2 : ℝ) := by 
          rw [h1]
        have h3 : sqrt (1/2 : ℝ) = sqrt 2 / 2 := by
          rw [show (1/2 : ℝ) = (2 : ℝ) / (2^2 : ℝ) by ring]
          field_simp [show (2 : ℝ) > 0 by norm_num]
        field_simp [h2, h3]
        <;> ring_nf <;> norm_num
      linarith 
  · -- Show that √2 is indeed a lower bound
    intro y
    rintro ⟨x, hx, hfx⟩
    rw [hf] at hfx
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 7 * x - 3 ≥ 0 := by linarith
    have h2 : Real.sqrt (7 * x - 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : x > 0 := by linarith
    have h4 : Real.sqrt (7 * x - 3) / x ≥ 0 := by positivity
    have h5 : Real.sqrt (7 * x - 3) / x ≥ Real.sqrt 2 := by
      have h5 : Real.sqrt (7 * x - 3) ≥ Real.sqrt 2 * x := by
        have h8 : Real.sqrt 2 * x ≥ 0 := mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (by linarith)
        have h9 : (Real.sqrt 2 * x) ^ 2 ≤ (Real.sqrt (7 * x - 3)) ^ 2 := by
          have h10 : (Real.sqrt (7 * x - 3)) ^ 2 = 7 * x - 3 := by
            rw [Real.sq_sqrt]
            linarith
          have h11 : (Real.sqrt 2 * x) ^ 2 = (Real.sqrt 2) ^ 2 * x ^ 2 := by ring
          have h12 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          rw [h11, h12] at *
          nlinarith [h10, sq_nonneg (x - 1 / 2), sq_nonneg (x - 3)]
        have h13 : Real.sqrt 2 * x ≤ Real.sqrt (7 * x - 3) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (7 * x - 3 : ℝ) by linarith),
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
            Real.sqrt_nonneg (7 * x - 3), Real.sqrt_nonneg 2]
        linarith
      have h6 : Real.sqrt (7 * x - 3) / x ≥ Real.sqrt 2 := by
        apply (le_div_iff₀' (by linarith)).mpr
        linarith [h5]
      linarith
    have h6 : Real.sqrt (7 * x - 3) / x = y := by
      simpa using hfx
    linarith [h6, h5]
    all_goals linarith