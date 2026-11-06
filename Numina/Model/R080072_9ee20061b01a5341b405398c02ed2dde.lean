import Mathlib

open Real

theorem inequalities_304210 :
    (∀ a b c : ℝ, a = b ∧ b = c → a^3 + b^3 + c^3 ≥ 3 * a * b * c) ∧
    ¬(∀ a b c : ℝ, a^3 + b^3 + c^3 = 3 * a * b * c → a = b ∧ b = c) := by
  constructor
  · -- Show that $a = b = c$ is sufficient
    intro a b c hab
    rcases hab with ⟨ha, hb⟩ -- ha: a = b, hb: b = c
    have h1 : a = b := ha
    have h2 : b = c := hb
    have h3 : a = c := by linarith
    rw [show b = a by linarith [h1], show c = a by linarith [h1, h2]]
    nlinarith [sq_nonneg (a - a : ℝ), sq_nonneg (a - a : ℝ), sq_nonneg (a - a : ℝ)]
  · -- Show that $a = b = c$ is not necessary
    intro h
    specialize h 1 1 (-2)
    norm_num at h
    all_goals
      norm_num at h ⊢
      all_goals
        tauto