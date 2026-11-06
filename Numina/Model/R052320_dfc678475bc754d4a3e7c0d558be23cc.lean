import Mathlib

theorem algebra_266487 (p q r s : ℕ) (h₀ : p ≠ 0) (h₁ : q ≠ 0) (h₂ : r ≠ 0) (h₃ : s ≠ 0)
    (h₄ : p ≠ q) (h₅ : p ≠ r) (h₆ : p ≠ s) (h₇ : q ≠ r) (h₈ : q ≠ s) (h₉ : r ≠ s)
    (h₁₀ : p ∈ Finset.Icc 1 4) (h₁₁ : q ∈ Finset.Icc 1 4) (h₁₂ : r ∈ Finset.Icc 1 4)
    (h₁₃ : s ∈ Finset.Icc 1 4) :
    p^q + r^s ≤ 83 := by
  rw [Finset.mem_Icc] at h₁₀ h₁₁ h₁₂ h₁₃
  rcases h₁₀ with ⟨hp1, hp2⟩
  rcases h₁₁ with ⟨hq1, hq2⟩
  rcases h₁₂ with ⟨hr1, hr2⟩
  rcases h₁₃ with ⟨hs1, hs2⟩
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;> norm_num
  <;> try { contradiction }
  <;> omega