import Mathlib

theorem algebra_608744 : IsGreatest { r | ∃ x : ℝ, r = (2:ℝ) ^ (x * (1 - x))} (2 ^ ((1:ℝ) / 4)) := by
  constructor
  · -- Show that 2 ^ (1 / 4) is in the set.
    use 1 / 2
    norm_num
  · -- Show that 2 ^ (1 / 4) is an upper bound.
    intro r hr
    rcases hr with ⟨x, hx⟩
    have h1 : x * (1 - x) ≤ (1 / 4 : ℝ) := by
      have h2 : (x - 1 / 2) ^ 2 ≥ 0 := by
        apply sq_nonneg
      nlinarith
    have h2 : (2 : ℝ) ^ (x * (1 - x)) ≤ (2 : ℝ) ^ ((1 / 4 : ℝ) ) := by
      apply Real.rpow_le_rpow_of_exponent_le 
      · -- Show that 2 ≥ 1
        norm_num
      · -- Show that x * (1 - x) ≤ (1 / 4 : ℝ)
        linarith [h1]
    have hr' : r = (2: ℝ) ^ (x * (1 - x)) := by linarith [hx]
    rw [hr']
    all_goals linarith [h2]