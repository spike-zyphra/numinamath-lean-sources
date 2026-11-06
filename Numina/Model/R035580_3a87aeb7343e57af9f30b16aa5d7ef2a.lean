import Mathlib

theorem number_theory_607816:
    IsLeast {β : ℕ | 0 < β ∧ ∃ α : ℕ, 0 < α ∧ 43 / (197 : ℚ) < α / (β : ℚ) ∧ α / (β : ℚ) < 17 / (77 : ℚ)} 32 := by
  simp [IsLeast, lowerBounds]
  refine' ⟨?_, ?_⟩
  · -- Show 32 with α=7 is a valid pair
    use 7
    norm_num
  · -- Show that any β with a valid α must be ≥ 32
    intro β hβ α hα h₀ h₁
    have h₂ : 43 * (β : ℚ) < 197 * (α : ℚ) := by
      have h₀' : (43 : ℚ) / 197 < (α : ℚ) / (β : ℚ) := h₀
      apply (div_lt_div_iff₀ (by norm_cast) (by norm_cast)).mp at h₀'
      ring_nf at h₀' ⊢
      linarith
    have h₃ : 77 * (α : ℚ) < 17 * (β : ℚ) := by
      have h₁' : (α : ℚ) / (β : ℚ) < (17 : ℚ) / (77 : ℚ) := h₁
      apply (div_lt_div_iff₀ (by norm_cast) (by norm_cast)).mp at h₁'
      ring_nf at h₁' ⊢
      linarith
    have h₄ : 43 * (β : ℕ) < 197 * (α : ℕ) := by
      exact_mod_cast h₂
    have h₅ : 77 * (α : ℕ) < 17 * (β : ℕ) := by
      exact_mod_cast h₃
    by_cases h₆ : β > 31
    · -- β > 31, contradicts as we need difference for β ≤ 31
      linarith
    · -- β ≤ 31
      have h₇ : β ≤ 31 := by linarith
      have h₈ : α < 7 := by
        nlinarith
      interval_cases α <;> try { 
        omega
      }
      all_goals
        interval_cases β
        all_goals 
          omega