import Mathlib

theorem calculus_131451 (ε : ℝ) (hε : ε > 0) : ∃ δ, δ > 0 ∧ ∀ x, (|x - 1 / 3| < δ ∧ x ≠ 1 / 3) → |(3 * x ^ 2 + 17 * x - 6) / (x - 1 / 3) - 19| < ε := by 
  use ε / 3 
  constructor 
  · -- Show δ > 0 
    linarith 
  · -- Now prove the main part 
    intro x h 
    rcases h with ⟨h1, h2⟩ 
    have h3 : x - 1 / 3 ≠ 0 := by 
      intro h4 
      apply h2 
      linarith 
    have eq1 : (3 * x ^ 2 + 17 * x - 6) / (x - 1 / 3) = 3 * x + 18 := by 
      have h4 : x - 1 / 3 ≠ 0 := h3
      have eq2 : (3 * x ^ 2 + 17 * x - 6) = (3 * x - 1) * (x + 6) := by 
        ring 
      have eq3 : x - 1 / 3 = (3 * x - 1) / 3 := by 
        ring_nf 
      rw [eq2, eq3] 
      have h5 : (3 * x - 1) ≠ 0 := by 
        by_contra h 
        have h6 : x = 1 / 3 := by 
          linarith 
        contradiction 
      field_simp [h5] 
      <;> ring 
    rw [eq1] 
    have h7 : |(3 * x + 18 : ℝ) - 19| = 3 * |x - 1 / 3| := by 
      have h8 : (3 * x + 18 : ℝ) - 19 = 3 * (x - 1 / 3) := by 
        linarith 
      rw [h8] 
      have h9 : |(3 * (x - 1 / 3 : ℝ))| = 3 * |(x - 1 / 3 : ℝ)| := by 
        calc 
          |(3 * (x - 1 / 3 : ℝ))| = |(3 : ℝ)| * |(x - 1 / 3 : ℝ)| := by 
            rw [abs_mul]
          _ = (3 : ℝ) * |(x - 1 / 3 : ℝ)| := by 
            norm_num 
          _ = 3 * |(x - 1 / 3 : ℝ)| := by 
            ring 
      linarith [h9] 
    have h8 : |x - 1 / 3| < ε / 3 := by 
      linarith [h1]
    have h9 : |(3 * x + 18 : ℝ) - 19| < ε := by 
      linarith [h7, h8] 
    simpa using h9