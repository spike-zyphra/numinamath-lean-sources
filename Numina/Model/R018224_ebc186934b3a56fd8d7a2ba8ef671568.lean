import Mathlib

theorem algebra_279083 (f : ℝ → ℝ) :
    (∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) ↔ ∀ x, f x = x + 1 := by
  constructor
  · -- Assume the functional equation, prove f(x) = x + 1.
    intro h
    have h1 : ∀ y, f 1 = f 0 * f y - f y + 2 := by
      intro y
      specialize h 0 y
      norm_num at h ⊢
      simpa using h
    have h2 := h1 0
    have eq1 : f 1 = f 0 * f 0 - f 0 + 2 := by
      simpa using h2
    have h3 := h1 1
    have eq2 : f 1 = f 0 * f 1 - f 1 + 2 := by
      simpa using h3
    have eq3 : f 1 * (2 - f 0) = 2 := by
      nlinarith
    have eq4 : f 0 ^ 3 - 3 * f 0 ^ 2 + 4 * f 0 - 2 = 0 := by
      nlinarith [sq_nonneg (f 1 - 2), sq_nonneg (f 0 - 1), sq_nonneg (f 0 - 2), sq_nonneg (f 1 - 1)]
    have h5 : f 0 = 1 := by
      have h6 : f 0 ^ 3 - 3 * f 0 ^ 2 + 4 * f 0 - 2 = 0 := eq4
      have h7 : f 0 ^ 3 - 3 * f 0 ^ 2 + 4 * f 0 - 2 = (f 0 - 1) * (f 0 ^ 2 - 2 * f 0 + 2) := by ring
      rw [h7] at h6
      cases' (mul_eq_zero.mp h6) with h8 h9
      · -- Case f 0 - 1 = 0, so f 0 = 1
        linarith
      · -- Case f 0 ^ 2 - 2 * f 0 + 2 = 0
        have h10 : f 0 ^ 2 - 2 * f 0 + 2 = 0 := by linarith
        have h11 : (f 0 - 1) ^ 2 ≥ 0 := sq_nonneg (f 0 - 1)
        nlinarith
    have eq5 : f 0 = 1 := h5
    have eq6 : f 1 = 2 := by
      rw [h5] at eq1
      nlinarith [h5, sq_nonneg (f 0 - 1)]
    intro x
    have eq8 : f 1 = f x * f 0 - f 0 - x + 2 := by 
      specialize h x 0
      norm_num at h ⊢
      simpa using h
    rw [eq6, eq5] at eq8
    nlinarith
  · -- Assume f(x) = x + 1, prove the functional equation.
    intro hf x y
    rw [hf (x * y + 1), hf x, hf y]
    ring_nf