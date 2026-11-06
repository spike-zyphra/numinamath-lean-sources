import Mathlib

theorem algebra_608834 (δ : ℝ × ℝ → ℝ) (hδ : ∀ a b, 0 < a → 0 < b → δ (a, b) = a + b + 2 * Real.sqrt (a * b)) :
    {x : ℝ | 0 < x ∧ δ (x ^ 2, 9 * x) = 121} = {(31 - 3 * Real.sqrt 53) / 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ∈ { ... | 0 < x ∧ δ (x ^ 2, 9 * x) = 121 }
    rintro ⟨hx_pos, h_eq⟩
    have h1 : δ (x ^ 2, 9 * x) = x ^ 2 + 9 * x + 2 * Real.sqrt (x ^ 2 * (9 * x)) := by
      apply hδ
      all_goals
        nlinarith
    rw [h1] at h_eq
    have h2 : Real.sqrt (x ^ 2 * (9 * x)) = 3 * x * Real.sqrt x := by
      have h3 : x ^ 2 * (9 * x) = 9 * (x ^ 3) := by ring
      rw [h3]
      have h4 : Real.sqrt (9 * (x ^ 3)) = 3 * x * Real.sqrt x := by
        have h5 : Real.sqrt (9 * (x ^ 3)) = Real.sqrt ((3 * x) ^ 2 * x) := by
          ring_nf
        rw [h5]
        have h6 : Real.sqrt ((3 * x) ^ 2 * x) = Real.sqrt ((3 * x) ^ 2) * Real.sqrt x := by
          rw [Real.sqrt_mul (by positivity)]
        rw [h6]
        have h7 : Real.sqrt ((3 * x) ^ 2) = 3 * x := by
          rw [Real.sqrt_sq (by nlinarith)]
        rw [h7]
      exact h4
    rw [h2] at h_eq
    have h3 : (x + 3 * Real.sqrt x) ^ 2 = 121 := by
      nlinarith [h_eq, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h4 : x + 3 * Real.sqrt x = 11 := by
      nlinarith [h3, Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h6 : Real.sqrt x = (-3 + Real.sqrt 53) / 2 := by
      nlinarith [h4, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ (53 : ℝ) by norm_num), Real.sqrt_nonneg (53)]
    have h7 : x = (31 - 3 * Real.sqrt 53) / 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (53 : ℝ) by norm_num), Real.sqrt_nonneg x, Real.sqrt_nonneg (53), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), h6]
    linarith [h7]
  · -- Show that (31 - 3 * Real.sqrt 53) / 2 satisfies the conditions
    intro h_eq
    have hx1 : (31 - 3 * Real.sqrt 53) / 2 > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (53 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (53 : ℝ) by norm_num)]
    have hx2 : x > 0 := by
      rw [h_eq]
      linarith [hx1]
    constructor
    · -- Show 0 < x
      linarith [hx2]
    · -- Show δ (x ^ 2, 9 * x) = 121
      have h1 : δ (x ^ 2, 9 * x) = x ^ 2 + 9 * x + 2 * Real.sqrt (x ^ 2 * (9 * x)) := by
        apply hδ
        all_goals
          nlinarith [hx2]
      rw [h1]
      have h2 : Real.sqrt (x ^ 2 * (9 * x)) = 3 * x * Real.sqrt x := by
        have h3 : x ^ 2 * (9 * x) = 9 * (x ^ 3) := by ring
        rw [h3]
        have h4 : Real.sqrt (9 * (x ^ 3)) = 3 * x * Real.sqrt x := by
          have h5 : Real.sqrt (9 * (x ^ 3)) = Real.sqrt ((3 * x) ^ 2 * x) := by
            ring_nf
          rw [h5]
          have h6 : Real.sqrt ((3 * x) ^ 2 * x) = Real.sqrt ((3 * x) ^ 2) * Real.sqrt x := by
            rw [Real.sqrt_mul (by positivity)]
          rw [h6]
          have h7 : Real.sqrt ((3 * x) ^ 2) = 3 * x := by
            rw [Real.sqrt_sq (by nlinarith)]
          rw [h7]
        exact h4
      rw [h2]
      have h_eq1 : x = (31 - 3 * Real.sqrt 53) / 2 := by
        linarith [h_eq]
      have h6 : Real.sqrt x = (-3 + Real.sqrt 53) / 2 := by
        have h7 : x = (31 - 3 * Real.sqrt 53) / 2 := h_eq1
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by nlinarith), Real.sqrt_nonneg (53), Real.sq_sqrt (show (0 : ℝ) ≤ (53 : ℝ) by norm_num), sq_nonneg (Real.sqrt x - (-3 + Real.sqrt 53) / 2)]
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by nlinarith), Real.sqrt_nonneg (53), Real.sq_sqrt (show (0 : ℝ) ≤ (53 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by nlinarith), h6]