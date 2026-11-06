import Mathlib

theorem inequalities_189745 (x : ℕ) (hx : x ≠ 1) :
    (5 * x + 1) / (x - 1 : ℝ) > 2 * x + 2 ↔ x = 2 := by
  constructor
  · -- Assume (5 * x + 1) / (x - 1 : ℝ) > 2 * x + 2, prove x = 2
    intro h
    by_cases h2 : x > 1
    · -- x > 1, so x ≥ 2
      have h3 : (x : ℝ) > (1 : ℝ) := by
        have h4 : x > 1 := h2
        exact_mod_cast h4
      have h4 : (x - 1 : ℝ) > 0 := by
        have h5 : (x : ℝ) > 1 := h3
        linarith
      have h5 : (5 * (x : ℝ) + 1) / (x - 1 : ℝ) > 2 * (x : ℝ) + 2 := by
        simpa using h
      have h6 : (5 * (x : ℝ) + 1) > (2 * (x : ℝ) + 2) * (x - 1 : ℝ) := by
        have h7 : (x - 1 : ℝ) > 0 := h4
        apply (lt_div_iff₀ h7).mp at h5
        linarith
      have h7 : (2 * (x : ℝ)^2 - 5 * (x : ℝ) - 3) < 0 := by
        nlinarith
      have h8 : (x : ℝ) < (3 : ℝ) := by 
        nlinarith [sq_nonneg ((x : ℝ) - 3 : ℝ), sq_nonneg ((x : ℝ) + (1 : ℝ) / 2)]
      have h9 : x < 3 := by 
        by_contra h'
        push_neg at h'
        have h10 : x ≥ 3 := by linarith
        have h11 : (x : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h10
        nlinarith
      have h10 : x = 2 := by
        linarith
      linarith
    · -- x ≤ 1, so x = 0
      have h3 : x ≤ 1 := by linarith
      have h4 : x < 1 := by
        by_contra h'
        push_neg at h'
        have h5 : x = 1 := by linarith
        contradiction
      have h5 : x = 0 := by linarith
      rw [show (x : ℝ) = (0 : ℝ) by exact_mod_cast h5] at h
      norm_num at h
  · -- Assume x = 2, prove (5 * x + 1) / (x - 1 : ℝ) > 2 * x + 2
    intro h
    rw [h]
    norm_num