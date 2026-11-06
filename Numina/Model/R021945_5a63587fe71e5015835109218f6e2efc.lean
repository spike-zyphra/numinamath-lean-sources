import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_302566 {k : ℝ} (hk : 0 < k ∧ k < 1)
  (f : ℝ → ℝ) (hf : f = λ x => x - k * sqrt (x^2 - 1)) :
  ∀ x ≥ 1, f x ≥ sqrt (1 - k^2) ∧
  (∃ x ≥ 1, f x = sqrt (1 - k^2)) := by
  intro x hx
  have hk1 : 0 < k := hk.1
  have hk2 : k < 1 := hk.2
  have h1 : 0 < 1 - k ^ 2 := by nlinarith
  constructor
  · -- Show that $f x \ge \sqrt {1 - k^2}$.
    rw [hf]
    have h2 : x ^ 2 ≥1 := by nlinarith
    have h4 : sqrt (x^2 -1) ≥0 := Real.sqrt_nonneg (x^2-1)
    have h6 : (sqrt (1 -k^2)) ^2 = 1 -k^2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h11 : x - k * sqrt (x^2 -1) ≥ sqrt (1 -k^2) := by
      have h7 : (x - k * sqrt (x^2 -1)) ^2 ≥ (sqrt (1 -k^2)) ^2 := by
        have h8 : (x - k * sqrt (x^2 - 1)) ^2 = x^2 - 2 * k * x * sqrt (x^2 -1) + k^2 * (sqrt (x^2 -1) ^2) := by
          ring
        have h9 : sqrt (x^2 -1) ^2 = x^2 -1 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h10 : (sqrt (1 -k^2)) ^2 = 1 -k^2 := h6
        rw [h8, h9, h10]
        nlinarith [sq_nonneg (x^2 -1 -k^2), sq_nonneg (x - 1 / sqrt (1 -k^2)), 
          sq_nonneg (sqrt (x^2 -1) - k / sqrt (1 -k^2)), 
          sq_nonneg (x * k - sqrt (x^2 -1)), 
          Real.sqrt_nonneg (x^2 -1), Real.sqrt_nonneg (1 -k^2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 -1 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 -k^2 : ℝ) by nlinarith), 
          mul_pos hk1 (show (0 : ℝ) < (1 -k : ℝ) by linarith)
        ]
      have h13 : x - k * sqrt (x^2 -1) ≥0 := by
        have h14 : sqrt (x^2 -1) ≤x := by
          have h15 : (sqrt (x^2 -1)) ^2 ≤ (x) ^2 := by
            have h16 : (sqrt (x^2 -1)) ^2 = x^2 -1 := by
              rw [Real.sq_sqrt]
              nlinarith
            nlinarith
          nlinarith [Real.sqrt_nonneg (x^2 -1)]
        nlinarith [Real.sqrt_nonneg (x^2 -1), mul_pos hk1 (show (0: ℝ) < (1-k : ℝ) by linarith)]
      have h7' : sqrt (1 -k^2) ≥0 := Real.sqrt_nonneg (1 -k^2)
      nlinarith [h7, h13, Real.sqrt_nonneg (1-k^2), sq_nonneg (sqrt (1 -k^2) - (x -k * sqrt (x^2 -1)))
        ]
    simpa using h11
  · -- Show that ∃ x ≥ 1, f x = sqrt (1 -k^2)
    use 1 / sqrt (1 -k^2)
    constructor
    · -- Show that 1 / sqrt (1 -k^2) ≥1
      have h1_pos : sqrt (1 -k^2) >0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      have h2_pos : sqrt (1 -k^2) <1 := by
        nlinarith [Real.sqrt_nonneg (1 -k^2), Real.sq_sqrt (show (1 -k^2 : ℝ) ≥0 by nlinarith)]
      have h3_pos : (1 / sqrt (1 -k^2)) ≥1 := by
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      exact h3_pos
    · -- Show that f (1 / sqrt (1 -k^2)) = sqrt (1 -k^2)
      rw [hf]
      have h1_pos : sqrt (1 -k^2) >0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      have h2 : sqrt ((1 / sqrt (1 -k^2)) ^2 -1) = k / sqrt (1 -k^2) := by
        have h3 : (1 / sqrt (1 -k^2)) ^2 -1 = (k ^2) / (1 -k^2) := by
          field_simp
          <;> nlinarith [Real.sqrt_nonneg (1 -k^2), Real.sq_sqrt (show (1 -k^2 : ℝ) ≥0 by nlinarith)]
        rw [h3]
        have h4 : sqrt ((k ^2) / (1 -k^2)) = sqrt (k ^ 2) / sqrt (1 -k^2) := by
          field_simp [Real.sqrt_div]
        rw [h4]
        have h5 : sqrt (k ^2) = k := by
          rw [Real.sqrt_sq (by linarith)]
        rw [h5]
      have h3 : (1 / sqrt (1 -k^2) -k * sqrt ((1 / sqrt (1 -k^2)) ^2 -1)) = sqrt (1 -k^2) := by
        rw [h2]
        field_simp
        <;> nlinarith [Real.sqrt_nonneg (1 -k^2), Real.sqrt_nonneg (k ^2), Real.sq_sqrt (show (1 -k^2 : ℝ) ≥0 by nlinarith), Real.sq_sqrt (show (k ^2 : ℝ) ≥0 by nlinarith)]
      simpa using h3