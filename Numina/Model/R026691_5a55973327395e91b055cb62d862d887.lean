import Mathlib

theorem algebra_190966 :
    ∃ (f g : ℝ → ℝ), f 0 = 7 ∧ ∀ x, g x * f (x + 1) / f x = g (2 * x) + 1 := by
  use (fun (x : ℝ) => 7 * (2 : ℝ) ^ x)
  use (fun (x : ℝ) => 1)
  constructor
  · -- Show that f 0 = 7
    norm_num
  · -- Show that ∀ x, g x * f (x + 1) / f x = g (2 * x) + 1
    intro x
    have h1 : (7 * (2 : ℝ) ^ (x + 1)) / (7 * (2 : ℝ) ^ x) = 2 := by
      have hx1 : (2 : ℝ) ^ (x + 1) = (2 : ℝ) ^ x * 2 := by
        rw [Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [hx1]
      have hx2 : 7 * ((2 : ℝ) ^ x * 2) = 2 * (7 * (2 : ℝ) ^ x) := by ring
      rw [hx2]
      field_simp [show (7 * (2 : ℝ) ^ x) ≠ 0 by positivity]
      <;> ring
    have h2 : (1 : ℝ) * (7 * (2 : ℝ) ^ (x + 1)) / (7 * (2 : ℝ) ^ x) = (1 : ℝ) + 1 := by
      calc
        (1 : ℝ) * (7 * (2 : ℝ) ^ (x + 1)) / (7 * (2 : ℝ) ^ x) = (7 * (2 : ℝ) ^ (x + 1)) / (7 * (2 : ℝ) ^ x) := by ring_nf
        _ = 2 := h1
        _ = (1 : ℝ) + 1 := by norm_num
    simp_all [h2]
    <;> linarith