import Mathlib

theorem algebra_297967 (k : ℝ) (α β : ℝ) (h₁ : α ≠ β)
    (h₂ : α ∈ Set.Ioo 0 1) (h₃ : β ∈ Set.Ioo 1 2)
    (h₄ : 7 * α ^ 2 - (k + 13) * α + k ^ 2 - k - 2 = 0)
    (h₅ : 7 * β ^ 2 - (k + 13) * β + k ^ 2 - k - 2 = 0) :
    -2 < k ∧ k < -1 ∨ 3 < k ∧ k < 4 := by
  rw [Set.mem_Ioo] at h₂ h₃
  rcases h₂ with ⟨hα₁, hα₂⟩
  rcases h₃ with ⟨hβ₁, hβ₂⟩

  have h6 : 7 * (α ^ 2 - β ^ 2) - (k + 13) * (α - β) = 0 := by
    nlinarith

  have h7 : (α - β) * (7 * (α + β) - (k + 13)) = 0 := by
    have h : 7 * (α ^ 2 - β ^ 2) - (k + 13) * (α - β) = 0 := by linarith
    have h8 : 7 * (α ^ 2 - β ^ 2) - (k + 13) * (α - β) = (α - β) * (7 * (α + β) - (k + 13)) := by ring
    rw [h8] at h
    linarith

  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Case where α = β, which contradicts α ≠ β
    have h9 : α = β := by linarith
    contradiction

  · -- Case where 7(α + β) - (k + 13) = 0
    have hk : k = 7 * (α + β) - 13 := by linarith

    rw [hk]
    by_cases h : α + β < 2
    · -- When α + β < 2
      have h12 : α + β < 2 := by linarith
      left
      constructor
      · -- -2 < k
        nlinarith
      · -- k < -1
        nlinarith
    · -- When α + β ≥ 2
      have h12 : α + β ≥ 2 := by linarith
      right
      constructor
      · -- 3 < k
        nlinarith
      · -- k < 4
        nlinarith