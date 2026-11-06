import Mathlib
import Mathlib.Tactic.NormNum

theorem algebra_93068 :
  ∀ c : ℕ, 0 < c →
    (12 * (4 * c) + 15 * (2 * c) + 10 * c : ℝ) / (4 * c + 2 * c + c) = 88 / 7 := by 
  intro c hc
  have h1 : (4 * c + 2 * c + c : ℝ) ≠ 0 := by 
    have hc' : (c : ℝ) > 0 := by exact_mod_cast hc
    have h2 : (4 * c + 2 * c + c : ℝ) > 0 := by
      have : (4 * c + 2 * c + c : ℝ) = 7 * (c : ℝ) := by ring
      rw [this]
      linarith
    positivity
  field_simp [h1]
  ring_nf
  <;> simp
  all_goals ring_nf <;> omega