import Mathlib

theorem number_theory_57757 :
    IsLeast {β : ℕ | ∃ α : ℕ, 0 < α ∧ 0 < β ∧ (16 / 37 : ℚ) < (α / β : ℚ) ∧ (α / β : ℚ) < (7 / 16 : ℚ)} 23 := by
  constructor
  · -- Show that 23 is in the set by demonstrating that (10, 23) satisfies the conditions
    use 10
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now prove minimality: if β < 23, then there's no α with 0 < α and β > 0 satisfying the inequalities
    intro β hβ
    rcases hβ with ⟨α, hα_pos, hβ_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h1' : (16 : ℚ) * (β : ℚ) < 37 * (α : ℚ) := by
      have h1_q : (16 / 37 : ℚ) < (α / β : ℚ) := by assumption
      have h3 : β ≠ 0 := by positivity
      have h4 : α ≠ 0 := by positivity
      have h5 : (16 : ℚ) * (β : ℚ) < 37 * (α : ℚ) := by
        have h6 : (16 : ℚ) / (37 : ℚ) < (α : ℚ) / (β : ℚ) := by
          linarith
        have h7 : (16 : ℚ) * (β : ℚ) < 37 * (α : ℚ) := by
          have h8 : (β : ℚ) > 0 := by positivity
          have h9 : (37 : ℚ) > 0 := by norm_num
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
          nlinarith
        linarith
      linarith
    have h2' : (16 : ℚ) * (α : ℚ) < 7 * (β : ℚ) := by
      have h2_q : (α / β : ℚ) < (7 / 16 : ℚ) := by assumption
      have h3 : β ≠ 0 := by positivity
      have h4 : α ≠ 0 := by positivity
      have h5 : (16 : ℚ) * (α : ℚ) < 7 * (β : ℚ) := by
        have h6 : (α : ℚ) / (β : ℚ) < (7 : ℚ) / (16 : ℚ) := by
          linarith
        have h7 : (16 : ℚ) * (α : ℚ) < 7 * (β : ℚ) := by
          have h8 : (β : ℚ) > 0 := by positivity
          have h9 : (16 : ℚ) > 0 := by norm_num
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
          nlinarith
        linarith
      linarith
    have h1_nat : 16 * β < 37 * α := by
      exact_mod_cast h1'
    have h2_nat : 16 * α < 7 * β := by
      exact_mod_cast h2'
    -- Now with h1_nat and h2_nat, we need to prove β ≥ 23 by contradiction
    -- Assume β < 23 - which means h fails
    interval_cases β <;> omega
    all_goals linarith