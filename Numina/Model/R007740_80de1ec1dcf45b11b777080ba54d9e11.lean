import Mathlib

theorem algebra_9357 (a : ℝ) :
    (∀ x ∈ Set.Ici 2, x^2 + (2 - a)*x + 4 - 2*a > 0) ↔ a < 3 := by
  constructor
  · -- Assume h: ∀ x ∈ Set.Ici 2, x^2 + (2 - a) * x + 4 - 2 * a > 0, prove a < 3
    intro h
    have h2 := h 2 (Set.mem_Ici.mpr (by norm_num))
    norm_num at h2
    linarith
  · -- Assume a < 3, prove ∀ x ∈ Set.Ici 2, x^2 + (2 - a) * x + 4 - 2 * a > 0
    intro ha x hx
    rw [Set.mem_Ici] at hx
    have h1 : x ≥ 2 := hx
    nlinarith [sq_nonneg (x - 2), sq_nonneg (a - 3), sq_nonneg (x * (a - 3)), sq_nonneg (x - 2 * (a - 3)), mul_nonneg (show 0 ≤ (x - 2 : ℝ) by linarith) (show 0 ≤ (x - 2 : ℝ) by linarith), mul_nonneg (show 0 ≤ (x - 2 : ℝ) by linarith) (show 0 ≤ (x - 2 : ℝ) by linarith)]