import Mathlib

theorem algebra_14457 (n : ℕ) (h₀ : n ∈ Finset.Icc 1 9) (h₁ : n + 2 ∈ Finset.Icc 1 9) (h₂ : n + 4 ∈ Finset.Icc 1 9)
    (h₃ : Odd n) (h₄ : Odd (n + 2)) (h₅ : Odd (n + 4)) (h₆ : n + (n + 2) + (n + 4) = (n * (n + 2) * (n + 4)) / 7) : n + 2 = 5 := by
  rw [Finset.mem_Icc] at h₀ h₁ h₂
  rcases h₀ with ⟨h₇, h₈⟩
  rcases h₁ with ⟨h₉, h₁₀⟩
  rcases h₂ with ⟨h₁₁, h₁₂⟩
  have h13 : n ≤ 5 := by linarith
  have h14 : n ≥ 1 := by linarith
  interval_cases n <;> norm_num at h₆ <;> omega