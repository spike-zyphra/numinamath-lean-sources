import Mathlib

theorem algebra_275227 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ x = a + b ∧ (1 + 25 / 100 : ℝ) * a > 5 * b} 6 := by
  constructor
  · -- We can take a = 5 and b = 1, then all conditions are satisfied.
    use 5, 1
    constructor
    · norm_num -- proves 5 > 0
    constructor
    · norm_num -- proves 1 > 0
    constructor
    · norm_num -- proves 6 = 5 + 1
    · norm_num -- proves (1 + 25 / 100 : ℝ) * (5 : ℝ) > 5 * (1 : ℝ)
  · -- Assume that x is in the set, we prove x >= 6.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx_eq, hineq⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 5 := by
      linarith [hx_eq, h]
    have h2 : b ≤ 5 := by
      linarith [hx_eq, h]
    have h3 : (a : ℝ) > 0 := by
      exact_mod_cast ha
    have h4 : (b : ℝ) > 0 := by
      exact_mod_cast hb
    have h5 : (a : ℝ) > 4 * (b : ℝ) := by
      have h6 : (a : ℝ) > 0 := by
        exact_mod_cast ha
      have h7 : (b : ℝ) > 0 := by
        exact_mod_cast hb
      have h8 : (1 + 25 / 100 : ℝ) * (a : ℝ) > 5 * (b : ℝ) := by
        simpa using hineq
      nlinarith -- Solves (1.25 * a) > (5 * b) to a > 4 * b
    have h6 : a > 4 * b := by
      by_contra h7
      push_neg at h7
      have h7' : (a : ℝ) ≤ 4 * (b : ℝ) := by
        exact_mod_cast h7
      linarith [h5, h7']
    have h7 : a + b ≤ 5 := by
      omega
    have h8 : 5 * b < (a + b : ℕ) := by
      omega
    have h9 : 5 * b < 5 := by
      linarith [h8, h7]
    omega -- Contradiction since b > 0 and b < 1 cannot both be true