import Mathlib

theorem algebra_2248 (a b : ℝ) (h : ∀ x y : ℝ, x + a * y + 1 = 0 → b * x - 2 * y + 1 = 0) :
    a = -2 ∧ b = 1 := by 
  have hb : b = 1 := by 
    specialize h (-1) 0 (by norm_num)
    linarith
  have ha : a = -2 := by
    specialize h (a - 1) (-1) (by 
      ring_nf <;> linarith
    )
    rw [hb] at h
    linarith
  exact ⟨ha, hb⟩