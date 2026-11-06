import Mathlib

open Real Set

theorem inequalities_323541 (x : ℝ) :
    max (19 * x + 1) (92 * x + 74) ≥ 0 ↔ x ∈ Ici (-37 / 46) := by
  simp only [mem_Ici]
  constructor
  · -- Forward: max(a, b) ≥ 0 → x ∈ Ici (-37 / 46)
    intro h
    by_cases h1 : 19 * x + 1 ≤ 92 * x + 74
    · -- If 19x + 1 ≤ 92x + 74, max = 92x + 74
      have h2 : max (19 * x + 1) (92 * x + 74) = 92 * x + 74 := by apply max_eq_right; linarith
      rw [h2] at h
      linarith
    · -- If 19x + 1 > 92x + 74, max = 19x + 1
      have h2 : max (19 * x + 1) (92 * x + 74) = 19 * x + 1 := by apply max_eq_left; linarith
      rw [h2] at h
      linarith
  · -- Backward: x ∈ Ici (-37 / 46) → max(a, b) ≥ 0
    intro h
    have hx : (-37 / 46 : ℝ) ≤ x := by linarith
    -- We need max(19 * x + 1, 92 * x + 74) ≥ 0
    have h1 : 92 * x + 74 ≥ 19 * x + 1 := by linarith
    have h2 : max (19 * x + 1) (92 * x + 74) = 92 * x + 74 := by apply max_eq_right; linarith
    rw [h2]
    linarith