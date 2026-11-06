import Mathlib

open Real

theorem negated_inequalities_81831 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b)^3 / (a^2 * b) ≥ 27 / 4 ∧ ((a + b)^3 / (a^2 * b) = 27 / 4 ↔ a = 2 * b) := by
  have h1 : (a + b)^3 / (a^2 * b) ≥ 27 / 4 := by
    have h2 : 0 < a^2 * b := by
      positivity
    have h3 : (a + b)^3 ≥ (27 / 4) * (a^2 * b) := by
      have h4 : 4 * ((a + b)^3) ≥ 27 * (a^2 * b) := by
        nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - 2 * a * b), sq_nonneg (a * (a - 2 * b)), sq_nonneg (b * (a - 2 * b)), mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a + 2 * b), sq_nonneg (2 * a - b)]
      linarith
    have h5 : (a + b)^3 / (a^2 * b) ≥ 27 / 4 := by
      have pos1 : 0 < a^2 * b := h2
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [h3]
    exact h5
  have h2 : (a + b)^3 / (a^2 * b) = 27 / 4 ↔ a = 2 * b := by
    constructor
    · -- Assume equality holds, prove a = 2 * b
      intro h_eq
      have h2 : 0 < a^2 * b := by
        positivity
      have h3 : 4 * ((a + b)^3) = 27 * (a^2 * b) := by
        have h2 : 0 < a^2 * b := h2
        have eq2 : (a + b)^3 / (a^2 * b) = 27 / 4 := h_eq
        have pos1 : 0 < a^2 * b := h2
        have eq3 : 4 * ((a + b)^3) = 27 * (a^2 * b) := by
          have eq4 : (a + b)^3 / (a^2 * b) = ((a + b)^3) / (a^2 * b) := by rfl
          rw [eq4] at eq2
          field_simp at eq2 ⊢
          nlinarith
        exact eq3
      -- From the equality, we must derive that a = 2b.
      have h4 : (a - 2 * b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - 2 * a * b), sq_nonneg (a * (a - 2 * b)), sq_nonneg (b * (a - 2 * b)), mul_pos ha hb, sq_nonneg (a - b), sq_nonneg (a + 2 * b), sq_nonneg (2 * a - b)]
      have h5 : a - 2 * b = 0 := by
        rw [sq_eq_zero_iff] at h4
        exact h4
      linarith
    · -- Assume a = 2 * b, prove the equality
      intro h_eq
      rw [h_eq]
      field_simp
      <;> ring
  exact ⟨h1, h2⟩