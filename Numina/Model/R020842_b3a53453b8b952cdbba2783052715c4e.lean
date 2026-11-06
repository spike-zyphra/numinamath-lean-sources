import Mathlib

theorem algebra_266435 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 1 / a + 1 / b + 1 / c + 1 / d = 1 / 6)
    (h₂ : 1 / a + 1 / b + 1 / d = 1 / 5)
    (h₃ : 1 / a + 1 / c + 1 / d = 1 / 4)
    (h₄ : 1 / b + 1 / c + 1 / d = 1 / 3) :
    1 / a + 1 / b + 1 / c = 1 / (2 + 14 / 23) := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  -- Compute the value of 1/c from h₁ and h₂
  have h₅ : 1 / c = 1 / 6 - 1 / 5 := by 
    have eq1 : 1 / c = (1 / a + 1 / b + 1 / c + 1 / d) - (1 / a + 1 / b + 1 / d) := by 
      ring_nf
    rw [eq1, h₁, h₂]
    all_goals linarith
  -- Show that 1/c is negative
  have h₆ : 1 / c < 0 := by 
    have h₇ : (1 / 6 : ℝ) < (1 / 5 : ℝ) := by 
      norm_num
    have h₈ : (1 / 6 : ℝ) - (1 / 5 : ℝ) < 0 := by linarith
    linarith [h₇, h₈, h₅]
  -- Show that 1/c must be positive from hc
  have h₈ : 1 / c > 0 := by
    apply div_pos
    norm_num
    all_goals linarith [hc]
  linarith [h₆, h₈]