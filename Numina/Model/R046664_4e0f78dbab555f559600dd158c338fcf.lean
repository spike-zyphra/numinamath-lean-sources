import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315368 (k : ℝ) :
  {x : ℤ | x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0} = {-2} ↔
  -3 ≤ k ∧ k < 2 := by

  constructor
  · -- Assume {x : ℤ | x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0} = {-2}, prove -3 ≤ k ∧ k < 2
    intro h_eq
    have h1 : -2 ∈ {x : ℤ | x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0} := by
      rw [h_eq]
      simp
    rcases h1 with ⟨h11, h12⟩
    have h2 : (3 : ℤ) ∉ {x : ℤ | x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0} := by
      rw [h_eq]
      simp
    simp at h2
    norm_num at h11 h12 h2
    constructor <;> linarith
  · -- Assume -3 ≤ k ∧ k < 2, prove {x : ℤ | x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0} = {-2}
    rintro ⟨hk1, hk2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume h: x^2 - x - 2 > 0 ∧ 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0, prove x = -2
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x < -1 ∨ x > 2 := by
        by_contra h'
        push_neg at h'
        have : x ≥ -1 := by omega
        have : x ≤ 2 := by omega
        interval_cases x <;> omega
      cases h3 with
      | inl h4 =>
        have h5 : x ≤ -2 := by omega
        by_cases h6 : x < -2
        · -- Case x < -2, so x ≤ -3
          have h4 : x ≤ -3 := by omega
          have h4' : (x : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h4
          nlinarith [sq_nonneg ((x : ℝ) + 2), sq_nonneg (k + 3), sq_nonneg (k - 2)]
        · -- Case x ≥ -2, so x = -2
          have h7 : x = -2 := by omega
          assumption
      | inr h4 =>
        have h6 : x ≥ 3 := by omega
        have h6' : (x : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h6
        nlinarith [sq_nonneg ((x : ℝ) + 2), sq_nonneg (k + 3), sq_nonneg (k - 2)]
    · -- Assume x = -2, prove h
      intro h_eq
      rw [h_eq]
      constructor
      · -- Check x = -2 satisfies x^2 - x - 2 > 0
        norm_num
      · -- Check x = -2 satisfies 2 * x^2 + (5 + 2 * k) * x + 5 * k < 0
        norm_num
        nlinarith