import Mathlib

theorem number_theory_93639 (a b c d : ℕ) (h₀ : 0 < a ∧ a ≤ 6) (h₁ : 0 < b ∧ b ≤ 6)
    (h₂ : 0 < c ∧ c ≤ 6) (h₃ : 0 < d ∧ d ≤ 6) (h₄ : a * b * c * d = 144) :
    a + b + c + d ≠ 18 := by
  rcases h₀ with ⟨ha_pos, ha_le⟩
  rcases h₁ with ⟨hb_pos, hb_le⟩
  rcases h₂ with ⟨hc_pos, hc_le⟩
  rcases h₃ with ⟨hd_pos, hd_le⟩

  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  <;> omega