import Mathlib

theorem algebra_18879 : IsMaxOn (fun (p : ℝ) ↦ (128 - 4 * p) * p) {p : ℝ | p ≤ 32} 16 := by
  unfold IsMaxOn
  intro p hp
  have h1 : p ≤ (32 : ℝ) := by
    simpa using hp
  have h2 : (128 - 4 * p) * p ≤ (128 - 4 * (16 : ℝ)) * (16 : ℝ) := by 
    nlinarith [sq_nonneg (p - 16)]
  simpa using h2