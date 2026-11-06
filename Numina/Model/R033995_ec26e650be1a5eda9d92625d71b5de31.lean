import Mathlib

theorem algebra_12080 : IsGreatest {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ x = (a + b)/c} (√2) := by
  constructor
  · -- Show that √2 is in the set.
    use 1, 1, Real.sqrt 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that √2 > 0
      positivity
    constructor
    · -- Show that 1^2 + 1^2 = (√2)^2
      have h1 : (1: ℝ) ^ 2 + (1: ℝ) ^ 2 = (Real.sqrt 2) ^ 2 := by
        norm_num [Real.sq_sqrt]
      linarith
    · -- Show that √2 = (1 + 1)/√2
      have h4 : (1 + 1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
        have h5 : Real.sqrt 2 > 0 := by positivity
        have h6 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        field_simp [h5, h6]
        <;> nlinarith
      linarith [h4]
  · -- Show that √2 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : (a + b) / c ≤ Real.sqrt 2 := by
      have h2 : (a + b) ^ 2 ≤ 2 * (c ^ 2) := by
        nlinarith [sq_nonneg (a - b), h1]
      have h4 : ((a + b) / c) ^ 2 ≤ (2 : ℝ) := by
        have h5 : c > 0 := hc
        have h6 : ((a + b) / c) ^ 2 = (a + b) ^ 2 / c ^ 2 := by
          field_simp [h5]
        rw [h6]
        have h7 : (a + b) ^ 2 ≤ 2 * c ^ 2 := h2
        have h8 : c ^ 2 > 0 := by
          positivity
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      have h5 : (a + b) / c ≤ Real.sqrt 2 := by
        have h6 : ((a + b) / c) ^ 2 ≤ (2 : ℝ) := h4
        have h7 : Real.sqrt 2 ≥ 0 := by positivity
        have h8 : (a + b) / c ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        nlinarith [h6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg ((a + b) / c - Real.sqrt 2)]
      exact h5
    have h3 : x ≤ Real.sqrt 2 := by
      linarith [h2, hx]
    linarith [h3]