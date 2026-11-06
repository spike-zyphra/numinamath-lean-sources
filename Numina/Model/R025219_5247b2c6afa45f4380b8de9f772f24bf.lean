import Mathlib

theorem algebra_112010 (a : ℝ) (m n : ℝ)
    (h₁ : ∃ x, m = x ∧ Real.exp (x - 1) + x ^ 3 - 2 = 0)
    (h₂ : ∃ x, n = x ∧ x ^ 2 - a * x - a + 3 = 0)
    (h₃ : |m - n| ≤ 1) :
    2 ≤ a ∧ a ≤ 3 := by
  rcases h₁ with ⟨x₁, hm_eq₁, h₁⟩
  rcases h₂ with ⟨x₂, hn_eq₂, h₂⟩
  have h4 : x₁ = 1 := by
    by_cases h5 : x₁ < 1
    · -- Assume x₁ < 1
      have h5_pos : Real.exp (x₁ - 1) > 0 := Real.exp_pos (x₁ - 1)
      -- Since x₁ < 1, we have (x₁ - 1) < 0
      -- So Real.exp (x₁ - 1) < 1
      have h6 : Real.exp (x₁ - 1) < 1 := by
        have h7 : Real.exp (x₁ - 1) < Real.exp (0 : ℝ) := Real.exp_strictMono (by linarith)
        rw [show Real.exp (0 : ℝ) = 1 by
          simp [Real.exp_zero]] at h7
        linarith
      have h6' : Real.exp (x₁ - 1) + x₁ ^ 3 < 2 := by
        -- Then Real.exp (x₁ - 1) + x₁ ^ 3 < 1 + 1 = 2
        by_cases h8 : x₁ ≤ (0 : ℝ)
        · -- Case x₁ ≤ 0
          have h9 : Real.exp (x₁ - 1) < 1 := h6
          nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₁ ^ 3), sq_nonneg ((x₁ - 1) : ℝ), Real.exp_pos (x₁ - 1)]
        · -- Case 0 < x₁ < 1
          have h9 : 0 < x₁ := by linarith
          have h10 : x₁ ^ 3 < 1 := by
            have h11 : x₁ < (1 : ℝ) := h5
            nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₁ - 1), sq_pos_of_pos h9]
          have h11_pos : Real.exp (x₁ - 1) > 0 := h5_pos
          nlinarith
      -- But Real.exp (x₁ - 1) + x₁ ^ 3 = 2 from h₁ 
      nlinarith
    by_cases h6 : x₁ > 1
    · -- Assume x₁ > 1
      have h6_pos : Real.exp (x₁ - 1) > 0 := Real.exp_pos (x₁ - 1)
      -- Since x₁ > 1, (x₁ - 1) > 0
      -- So Real.exp (x₁ - 1) > 1
      have h5_pos : Real.exp (x₁ - 1) > 1 := by
        have h6_pos' : Real.exp (x₁ - 1) > Real.exp (0 : ℝ) := Real.exp_strictMono (by linarith)
        rw [show Real.exp (0 : ℝ) = 1 by
          simp [Real.exp_zero]] at h6_pos'
        linarith
      have h6' : Real.exp (x₁ - 1) + x₁ ^ 3 > 2 := by
        have h7_pos : Real.exp (x₁ - 1) > 1 := h5_pos
        have h8_pos : x₁ ^ 3 > 1 := by
          have h5_pos : x₁ > (1 : ℝ) := h6
          nlinarith [sq_nonneg (x₁ ^ 2), sq_nonneg (x₁ - 1 : ℝ)]
        nlinarith
      -- But Real.exp (x₁ - 1) + x₁ ^ 3 = 2 from h₁
      nlinarith
    -- So now we conclude that x₁ = 1
    linarith
  have h5 : 0 ≤ x₂ ∧ x₂ ≤ 2 := by
    rw [show m = x₁ by linarith [hm_eq₁],
        show n = x₂ by linarith [hn_eq₂]] at h₃
    rw [show x₁ = 1 by linarith [h4]] at h₃
    cases abs_le.mp h₃ with
    | intro h6 h7 =>
      constructor
      · linarith
      · linarith
  rcases h5 with ⟨h7, h8⟩
  have h6 : 2 ≤ a ∧ a ≤ 3 := by
    have h9 : x₂ + 1 > 0 := by linarith
    have h7' : a = (x₂ ^ 2 + 3) / (x₂ + 1) := by
      field_simp
      nlinarith [h₂, show x₂ + 1 > 0 by linarith]
    rw [h7']
    constructor
    · -- Prove that 2 ≤ a
      have h1 : (x₂ ^ 2 + 3) / (x₂ + 1) ≥ 2 := by
        have h11 : x₂ + 1 > 0 := by linarith
        have h2 : x₂ ^ 2 + 3 ≥ 2 * (x₂ + 1) := by
          nlinarith [sq_nonneg (x₂ - 1)]
        apply (le_div_iff₀ h11).mpr
        nlinarith
      linarith
    · -- Prove that a ≤ 3
      have h2 : (x₂ ^ 2 + 3) / (x₂ + 1) ≤ 3 := by
        have h11 : x₂ + 1 > 0 := by linarith
        have h3 : x₂ ^ 2 + 3 ≤ 3 * (x₂ + 1) := by
          nlinarith [sq_nonneg (x₂ - 0)]
        apply (div_le_iff₀ h11).mpr
        nlinarith
      linarith
  exact h6
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith [Real.exp_pos (x₁ - 1)]
  <;> try nlinarith [h₁, h₂, abs_le.mp h₃, sq_nonneg (x₁ - 1 : ℝ),
      sq_nonneg (x₂ - 0 : ℝ), sq_nonneg (x₂ - 1 : ℝ)]
  <;> norm_num
  <;> norm_num
  <;> norm_num
  all_goals try nlinarith [abs_le.mp h₃]
  <;> try linarith
  <;> norm_num
  all_goals try nlinarith [h₁, h₂]
  <;> norm_num
  <;> linarith