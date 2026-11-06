import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_12318 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 4 + cos x ^ 2) :
    range f = {x | 3 / 4 ≤ x ∧ x ≤ 1} := by
  ext y
  simp [hf]
  constructor
  · -- First direction: if y in range, then y in [3/4, 1]
    rintro ⟨x, hx⟩
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    have h2 : cos x ^ 2 = 1 - sin x ^ 2 := by
      linarith [h1]
    have h3 : sin x ^ 4 + cos x ^ 2 = (sin x ^ 2) ^ 2 - sin x ^ 2 + 1 := by
      rw [h2]
      nlinarith
    have h4 : 0 ≤ sin x ^ 2 := by
      have h5 : -1 ≤ sin x := by
        linarith [neg_one_le_sin x, sin_le_one x]
      have h6 : sin x ≤ 1 := by
        linarith [neg_one_le_sin x, sin_le_one x]
      nlinarith [sq_nonneg (sin x)]
    have h5 : sin x ^ 2 ≤ 1 := by
      have h6 : -1 ≤ sin x := by
        linarith [neg_one_le_sin x, sin_le_one x]
      have h7 : sin x ≤ 1 := by
        linarith [neg_one_le_sin x, sin_le_one x]
      nlinarith [sq_nonneg (sin x)]
    have h7 : 3 / 4 ≤ (sin x ^ 2) ^ 2 - sin x ^ 2 + 1 := by
      nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (sin x)]
    have h9 : (sin x ^ 2) ^ 2 - sin x ^ 2 + 1 ≤ 1 := by
      nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (sin x), h4, h5]
    constructor
    · -- The lower bound
      nlinarith [h3, h7, hx]
    · -- The upper bound
      nlinarith [h3, h9, hx]
  · -- Now the reverse direction
    rintro ⟨hy1, hy2⟩
    use Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))
    have h1 : Real.sin (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) ^ 2 = (1 - Real.sqrt (4 * y - 3)) / 2 := by
      have h11 : 0 ≤ (1 - Real.sqrt (4 * y - 3)) / 2 := by
        nlinarith [Real.sqrt_nonneg (4 * y - 3), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * y - 3 by linarith [Real.sqrt_nonneg (4 * y - 3), sq_nonneg (Real.sqrt (4 * y - 3))]), 
          Real.sqrt_nonneg (4 * y - 3)]
      have h12 : Real.sin (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) = Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) := by
        apply Real.sin_arcsin
        · -- Show that sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) ≥ -1
          nlinarith [Real.sqrt_nonneg ((1 - Real.sqrt (4 * y - 3)) / 2), Real.sqrt_nonneg (4 * y - 3)]
        · -- Show that sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) ≤ 1
          have h11 : (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) : ℝ) ^ 2 = (1 - Real.sqrt (4 * y - 3)) / 2 := by
            rw [Real.sq_sqrt]
            linarith
          nlinarith [Real.sqrt_nonneg ((1 - Real.sqrt (4 * y - 3)) / 2), h11, Real.sqrt_nonneg (4 * y - 3)]
      have h4 : (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) : ℝ) ^ 2 = (1 - Real.sqrt (4 * y - 3)) / 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h12]
      linarith
    have h2 : (Real.cos (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 = (1 + Real.sqrt (4 * y - 3)) / 2 := by
      have h41 : (Real.cos (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 = 1 - (Real.sin (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 := by
        rw [Real.cos_sq']
      rw [h41, h1]
      all_goals 
        nlinarith [Real.sqrt_nonneg (4 * y - 3), Real.sqrt_nonneg ((1 - Real.sqrt (4 * y - 3)) / 2)]
    have h7 : (Real.sin (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 4 + (Real.cos (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 = y := by
      have h71 : (Real.sin (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 = (1 - Real.sqrt (4 * y - 3)) / 2 := h1
      have h72 : (Real.cos (Real.arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)))) ^ 2 = (1 + Real.sqrt (4 * y - 3)) / 2 := h2
      nlinarith [Real.sqrt_nonneg (4 * y - 3), Real.sq_sqrt (show (0 : ℝ) ≤ (4 * y - 3 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (4 * y - 3) - 0)]
    linarith [h7]