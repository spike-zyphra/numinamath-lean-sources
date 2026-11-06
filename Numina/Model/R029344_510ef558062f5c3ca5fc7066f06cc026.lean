import Mathlib

open Real

theorem inequalities_151785 {a : Fin 4 → ℝ} (ha : StrictMono a)
    (ha1 : ∀ i, 0 < a i) :
    ∃ x y, x ∈ Set.range a ∧ y ∈ Set.range a ∧ (2 + sqrt 3) * abs (x - y) < (x + 1) * (y + 1) + x * y := by
  use a 0, a 0
  constructor
  · -- Show that a 0 is in the range of a
    simp [Set.mem_range]
    <;> use 0
  constructor
  · -- Show that a 0 is in the range of a
    simp [Set.mem_range]
    <;> use 0
  have h1 : 0 < a 0 := ha1 0
  have h2 : (2 + Real.sqrt 3) * abs (a 0 - a 0) < (a 0 + 1) * (a 0 + 1) + (a 0) * (a 0) := by
    have h3 : abs (a 0 - a 0) = 0 := by
      simp
    rw [h3]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_pos_of_pos (show 0 < a 0 by linarith [h1]), sq_nonneg (a 0), Real.sqrt_nonneg 3]
  exact h2