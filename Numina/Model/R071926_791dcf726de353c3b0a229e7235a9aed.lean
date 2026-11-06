import Mathlib

theorem algebra_280265 (A B : ℕ) (h₀ : A ∈ Finset.Icc 10 99) (h₁ : B ∈ Finset.Icc 10 99)
    (h₂ : (2 / 7 : ℚ) * A = (2 / 3 : ℚ) * B) :
    A - B ≤ 56 := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨h₅, h₆⟩
  have h₇ : (A : ℚ) ≤ 99 := by exact_mod_cast h₄
  have h₈ : (B : ℚ) ≤ 99 := by exact_mod_cast h₆
  have h₇ : 3 * (A : ℚ) = 7 * (B : ℚ) := by
    field_simp at h₂ ⊢
    linarith
  have h₉ : 3 * (A : ℤ) = 7 * (B : ℤ) := by
    exact_mod_cast h₇
  omega