import Mathlib

open Real

theorem algebra_21059 {f : ℝ → ℝ} (hf : f = fun x => 1 / (x - 3)) :
    IsGreatest {x | x = 3 ∨ f x = 3} (10 / 3) := by

  have hf1 : ∀ x, f x = 1 / (x - 3) := by
    intro x
    rw [hf]

  constructor
  · -- Show 10/3 is in the set
    right
    rw [hf1]
    norm_num

  · -- Show that 10/3 is greatest in the set
    intro x hx
    rcases hx with (h | h)
    · -- Case x = 3
      rw [h]
      norm_num
    · -- Case f x = 3
      have h1 : f x = 3 := h
      rw [hf1 x] at h1
      by_contra h2
      push_neg at h2
      have eq1 : x - 3 ≠ 0 := by
        by_contra h3
        have : x = 3 := by linarith
        nlinarith
      field_simp [eq1] at h1
      nlinarith