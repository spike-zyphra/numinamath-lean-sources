import Mathlib

theorem algebra_199833 :
    {x : ℝ | 3 * x ^ 5 + 3 * x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 - x - 1 = 0 ∧
    3 * x ^ 5 - 3 * x ^ 4 + 2 * x ^ 3 - 2 * x ^ 2 - x + 1 = 0} = {1 / √3, -1 / √3} := by
  ext x
  simp
  rw [show 3 * x ^ 5 + 3 * x ^ 4 + 2 * x ^ 3 + 2 * x ^ 2 - x - 1 = (x + 1) * (3 * x ^ 2 - 1) * (x ^ 2 + 1) by ring,
      show 3 * x ^ 5 - 3 * x ^ 4 + 2 * x ^ 3 - 2 * x ^ 2 - x + 1 = (x - 1) * (3 * x ^ 2 - 1) * (x ^ 2 + 1) by ring]
  simp
  constructor
  . rintro ⟨h₁, h₂⟩
    have h₃ : ¬ (x + 1 = 0 ∧ x - 1 = 0) := by
      rintro ⟨h₃, h₄⟩
      linarith only [h₃, h₄]
    have h₄ : x ^ 2 + 1 ≠ 0 := by positivity
    have h₅ : 3 * x ^ 2 - 1 = 0 := by tauto
    field_simp
    rw [show 3 * x ^ 2 - 1 = (√3 * x + 1) * (√3 * x - 1) by ring_nf; simp] at h₅
    simp at h₅
    rcases h₅ with h₅ | h₅
    . right
      linarith only [h₅]
    . left
      linarith only [h₅]
  . rintro h₁
    have h₂ : 3 * x ^ 2 - 1 = 0 := by
      rcases h₁ with rfl | rfl
      . norm_num
      . ring_nf
        norm_num
    tauto
