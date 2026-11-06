import Mathlib

theorem algebra_6985 (a b c d : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : b ≠ c) (h₄ : b ≠ d) (h₅ : c ≠ d) (h₆ : a ∈ Finset.Icc 2 5) (h₇ : b ∈ Finset.Icc 2 5)
    (h₈ : c ∈ Finset.Icc 2 5) (h₉ : d ∈ Finset.Icc 2 5) :
    a^b - c^d ≤ 1016 := by
  rw [Finset.mem_Icc] at h₆ h₇ h₈ h₉
  rcases h₆ with ⟨ha2, hha5⟩
  rcases h₇ with ⟨hb2, hhb5⟩
  rcases h₈ with ⟨hc2, hhc5⟩
  rcases h₉ with ⟨hd2, hd5⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
    <;> norm_num at *
    <;> omega