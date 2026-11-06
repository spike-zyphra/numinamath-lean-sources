import Mathlib

theorem algebra_13632 : IsGreatest {x : ℝ | ∀ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d → a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + x * b * c + c * d} (3 / 2) := by
  constructor
  · -- Show that $3/2$ is in the set
    intro a b c d h
    rcases h with ⟨ha, hb, hc, hd⟩
    nlinarith [sq_nonneg (a - b / 2), sq_nonneg (d - c / 2), sq_nonneg (b - c)]
  · -- Show that $3/2$ is greatest in the set
    intro x hx
    have h1 := hx 1 2 2 1 (by norm_num)
    norm_num at h1 ⊢
    linarith