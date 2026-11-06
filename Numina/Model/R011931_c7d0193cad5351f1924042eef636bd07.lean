import Mathlib

theorem algebra_305180 (f : ℕ → ℤ) (hf : ∀x>0, f x = -x^3 + 100 * x^2 + x):
IsGreatest {y | ∃ x:ℕ, x > 0 ∧ f x = y} (f 67) := by

  constructor
  · -- Show f(67) is in the range
    use 67
    constructor
    · norm_num
    · -- Show f 67 = f 67
      rfl

  · -- Show f(67) is the greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hfx_eq : f x = -x^3 + 100 * x^2 + x := by 
      apply hf 
      exact hx 
    have h67 : f 67 = -67^3 + 100 * 67^2 + 67 := by
      apply hf 
      all_goals linarith 
    rw [show y = f x by linarith [hfx]] 
    rw [h67, hfx_eq]
    by_contra h
    push_neg at h
    have h2 : x ≤ 67 ∨ x > 67 := by omega
    rcases h2 with (h2 | h2)
    · -- Case where x ≤ 67 
      have h3 : x ≤ 67 := h2
      interval_cases x <;> norm_num at h ⊢ 
      <;> omega 
    · -- Case where x > 67
      have h3 : x > 67 := h2
      have h4 : (x:ℤ) > 67 := by 
        exact_mod_cast h3
      nlinarith [sq_nonneg ((x:ℤ) - 67: ℤ), sq_nonneg ((x:ℤ) - 68: ℤ), 
          sq_nonneg ((67:ℤ) - 66: ℤ), sq_nonneg ((67:ℤ) - 68: ℤ), 
          h4, sq_nonneg ((x:ℤ) ^ 2 - 67 ^ 2: ℤ)
          ]