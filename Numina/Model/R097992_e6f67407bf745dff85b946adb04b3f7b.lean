import Mathlib

theorem number_theory_275359 : IsLeast {p : ℕ | 0 < p ∧ ∃ k : ℤ, Real.sqrt (2^3 * 5 * p) = k} 10 := by
  constructor
  · -- Show that 10 is a valid p, with sqrt(2^3 * 5 * 10) = 20
    constructor
    · norm_num
    · use 20
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  · -- Show that 10 is the smallest
    intro p hp
    rcases hp with ⟨hp_pos, ⟨k, hk⟩⟩
    have h : (2^3 * 5 * p : ℝ) = (k : ℝ) ^ 2 := by
      calc
        (2^3 * 5 * p : ℝ) = (Real.sqrt (2^3 * 5 * p)) ^ 2 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
          all_goals linarith
        _ = (k : ℝ) ^ 2 := by
          rw [hk]
    have h1 : 2^3 * 5 * p = k ^ 2 := by
      norm_num at h ⊢
      have h2 : (k : ℝ) ^ 2 = (k ^ 2 : ℝ) := by norm_num
      rw [h2] at h
      have h3 : (2^3 * 5 * p : ℝ) = (k ^ 2 : ℝ) := by linarith
      exact_mod_cast h3
    by_contra h4
    push_neg at h4
    have h5 : k ^ 2 = 2^3 * 5 * p := by
      omega
    have h6 : k ≤ 20 := by
      nlinarith
    have h7 : k ≥ -20 := by
      nlinarith
    interval_cases k <;> omega