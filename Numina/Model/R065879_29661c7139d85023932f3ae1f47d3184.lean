import Mathlib

theorem algebra_206466 {p q : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q)
    (h1 : f p = 0) (h2 : f q = 0) :
    (p, q) = (0, 0) ∨ (p, q) = (-1 / 2, -1 / 2) ∨ (p, q) = (1, -2) := by
  simp [hf] at h1 h2
  have h3 : 2 * p^2 + q = 0 := by linarith
  have h4 : q^2 + q * (p + 1) = 0 := by nlinarith
  have h5 : q = -2 * p^2 := by linarith
  rw [h5] at h4
  have h6 : 2 * p^2 * (2 * p^2 - p - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with hp1 hp2
  · -- Case where 2p^2 = 0, so p = 0
    have hp : p = 0 := by
      nlinarith
    have hq : q = 0 := by
      rw [hp] at h5
      nlinarith
    left
    simp [hp, hq]
  · -- Case where 2p^2 - p - 1 = 0
    have h7 : 2 * p^2 - p - 1 = 0 := by linarith
    have h8 : (p - 1) * (2 * p + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h8) with hp3 hp4
    · -- Case p = 1
      have hp : p = 1 := by linarith
      have hq : q = -2 := by
        rw [hp] at h5
        nlinarith
      right
      right
      simp [hp, hq]
    · -- Case 2p + 1 = 0, so p = -1/2
      have hp : p = -1/2 := by linarith
      have hq : q = -1/2 := by
        rw [hp] at h5
        nlinarith
      right
      left
      simp [hp, hq]