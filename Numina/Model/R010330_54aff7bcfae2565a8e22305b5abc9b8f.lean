import Mathlib

theorem algebra_21541 :
    {(s, t) : ℝ × ℝ | s = 9 - 2 * t ∧ t = 3 * s + 1} = {(1, 4)} := by
  ext ⟨s, t⟩
  simp
  constructor
  · -- Assume the pair satisfies both equations, prove that (s, t) = (1, 4)
    rintro ⟨h₁, h₂⟩
    have ht : t = 4 := by
      linarith [h₁, h₂]
    have hs : s = 1 := by
      rw [ht] at h₁
      linarith
    exact ⟨hs, ht⟩
  · -- Assume (s, t) = (1, 4), prove that it satisfies both equations
    rintro ⟨rfl, rfl⟩
    constructor <;> norm_num