import Mathlib

theorem number_theory_61134 :
    IsLeast {β : ℕ | ∃ α : ℕ, α > 0 ∧ β > 0 ∧ (43 / 197 : ℝ) < (α / β : ℝ) ∧ (α / β : ℝ) < (17 / 77 : ℝ)} 32 := by
  constructor
  · -- Verify that (7, 32) is in the set
    use 7
    norm_num
  · -- Show that 32 is minimal
    intro β h
    rcases h with ⟨α, hα_pos, hβ_pos, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : (α : ℝ) > 0 := by exact_mod_cast (show (α : ℕ) > 0 by linarith)
    have h4 : (β : ℝ) > 0 := by exact_mod_cast (show (β : ℕ) > 0 by linarith)
    have h5 : (43 : ℝ) * (β : ℝ) < 197 * (α : ℝ) := by
      have h6 : (43 / 197 : ℝ) < (α / β : ℝ) := h1
      have h7 : (43 / 197 : ℝ) < (α / β : ℝ) := h6
      have h8 : (43 : ℝ) * (β : ℝ) < 197 * (α : ℝ) := by
        have h9 : (43 / 197 : ℝ) < (α / β : ℝ) := h6
        apply (lt_div_iff₀ (by linarith)).mp at h9
        linarith
      linarith
    have h7 : (77 : ℝ) * (α : ℝ) < 17 * (β : ℝ) := by
      have h8 : (α / β : ℝ) < (17 / 77 : ℝ) := h2
      have h9 : (α / β : ℝ) < (17 / 77 : ℝ) := h8
      have h10 : (77 : ℝ) * (α : ℝ) < 17 * (β : ℝ) := by
        have h11 : (α / β : ℝ) < (17 / 77 : ℝ) := h8
        apply (div_lt_iff₀ (by linarith)).mp at h11
        linarith
      linarith
    have h8 : 43 * β < 197 * α := by
      have h9 : (43 : ℝ) * (β : ℝ) < 197 * (α : ℝ) := h5
      norm_cast at h9 ⊢
      all_goals omega
    have h9 : 77 * α < 17 * β := by
      have h10 : (77 : ℝ) * (α : ℝ) < 17 * (β : ℝ) := h7
      norm_cast at h10 ⊢
      all_goals omega
    have h10 : β ≥ 32 := by
      by_contra h
      push_neg at h
      interval_cases β <;> omega
    linarith