import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_326879 (k : ℤ) (hroots : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1^2 + 4 * x1 + 3 * k - 1 = 0 ∧ x2^2 + 4 * x2 + 3 * k - 1 = 0 ∧ x1^2 + x2^2 ≥ (x1 * x2)) (hf : ∀ x > 0, (1 + 5 * k) / x > 0 ∧ ∀ x < 0, (1 + 5 * k) / x < 0) :
    k = 0 ∨ k = 1 := by
  have h1 : (1 + 5 * k : ℝ) > 0 := by
    have h2 := (hf 1 (by norm_num)).1
    norm_num at h2
    exact_mod_cast h2
  rcases hroots with ⟨x1, x2, hx12, h1', h2', h3⟩
  have h4 : x1 + x2 = -4 := by
    have eq3 : x1^2 + 4 * x1 + (3 * (k : ℝ) - 1) = 0 := by linarith
    have eq4 : x2^2 + 4 * x2 + (3 * (k : ℝ) - 1) = 0 := by linarith
    have eq5 : (x1 - x2) * (x1 + x2 + 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with h6 h7
    · -- Case where `x1 - x2 = 0`
      exfalso
      apply hx12
      linarith
    · -- Case where `x1 + x2 + 4 = 0`
      linarith
  have h5 : x1 * x2 = (3 * k - 1 : ℝ) := by
    have eq3 : x1^2 + 4 * x1 + (3 * (k : ℝ) - 1) = 0 := by linarith
    have eq4 : x2^2 + 4 * x2 + (3 * (k : ℝ) - 1) = 0 := by linarith
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by 
      intro h
      apply hx12
      linarith
    ), h4]
  have h13 : (k : ℝ) ≤ (19 / 9 : ℝ) := by
    have h14 : x1^2 + x2^2 ≥ x1 * x2 := h3
    have h15 : x1^2 + x2^2 = (x1 + x2)^2 - 2 * (x1 * x2) := by nlinarith
    rw [h15] at h14
    rw [h4, h5] at h14
    nlinarith
  have h7 : k ≤ 1 := by
    by_contra h
    push_neg at h
    have h8 : k ≥ 2 := by omega
    have h9 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h8
    have h10 : (20 - 12 * (k : ℝ) : ℝ) < 0 := by
      nlinarith
    nlinarith [sq_nonneg (x1 + 2 : ℝ), sq_nonneg (x2 + 2 : ℝ)]
  have h3' : k ≥ 0 := by
    have h5 : (k : ℝ) > (-1 / 5 : ℝ) := by linarith
    have h6 : k > -1 := by
      by_contra h
      push_neg at h
      have h7 : k ≤ -1 := by omega
      have h8 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h7
      nlinarith
    omega
  have h11 : k = 0 ∨ k = 1 := by omega
  exact h11