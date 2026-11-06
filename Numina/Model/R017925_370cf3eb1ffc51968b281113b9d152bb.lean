import Mathlib

theorem number_theory_145961 {x : ℝ} (hx6 : ∃ q : ℚ, x^6 = q) (hx7 : ∃ q : ℚ, x^7 = q) :
    ∃ q : ℚ, x = q := by
  rcases hx6 with ⟨q1, h1⟩
  rcases hx7 with ⟨q2, h2⟩
  have h3 : x^7 = x * x^6 := by ring
  rw [h3] at h2
  rw [show x^6 = (q1 : ℝ) by exact_mod_cast h1] at h2
  by_cases h : (q1 : ℝ) = 0
  · -- q1 = 0
    have h4 : x^6 = 0 := by
      have h5 : (q1 : ℝ) = 0 := by exact_mod_cast h
      linarith [h1, h5]
    have h5 : x = 0 := by
      have h6 : x^6 = 0 := h4
      have : x^6 = 0 := h6
      have : x = 0 := by
        have h7 : x ^ 6 = 0 := h6
        simp at h7 ⊢
        <;> nlinarith
      assumption
    use (0 : ℚ)
    rw [h5]
    all_goals norm_num
  · -- q1 ≠ 0
    have h4 : (q1 : ℝ) ≠ 0 := by exact_mod_cast h
    have h5 : x = (q2 / q1 : ℝ) := by
      have h6 : x * (q1 : ℝ) = (q2 : ℝ) := by
        exact_mod_cast h2
      have h7 : (q1 : ℝ) ≠ 0 := by exact_mod_cast h
      have : x = (q2 / q1 : ℝ) := by
        field_simp [h7] at h6 ⊢
        linarith
      assumption
    use (q2 / q1 : ℚ)
    rw [h5]
    all_goals norm_num