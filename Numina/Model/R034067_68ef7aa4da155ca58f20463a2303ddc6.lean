import Mathlib

theorem algebra_3540 (a b c : ℝ) (ha : a ≠ 0) (x : ℕ → ℝ)
    (hx : ∀ i ∈ Finset.range 7, x (i + 1) - x i = x 1 - x 0)
    (h : a * x 0 ^ 2 + b * x 0 + c = 51 ∧ a * x 1 ^ 2 + b * x 1 + c = 107 ∧
      a * x 2 ^ 2 + b * x 2 + c = 185 ∧ a * x 3 ^ 2 + b * x 3 + c = 285 ∧
      a * x 4 ^ 2 + b * x 4 + c = 407 ∧ a * x 5 ^ 2 + b * x 5 + c = 549 ∧
      a * x 6 ^ 2 + b * x 6 + c = 717) :
    a * x 3 ^ 2 + b * x 3 + c = 551 := by

  have h1 : x 1 - x 0 = x 1 - x 0 := by
    specialize hx 0 (by simp)
    simpa using hx

  have h2 : x 2 - x 1 = x 1 - x 0 := by
    specialize hx 1 (by simp)
    simpa using hx

  have h3 : x 3 - x 2 = x 1 - x 0 := by
    specialize hx 2 (by simp)
    simpa using hx

  have h4 : x 4 - x 3 = x 1 - x 0 := by
    specialize hx 3 (by simp)
    simpa using hx

  have h5 : x 5 - x 4 = x 1 - x 0 := by
    specialize hx 4 (by simp)
    simpa using hx

  have h6 : x 6 - x 5 = x 1 - x 0 := by
    specialize hx 5 (by simp)
    simpa using hx

  have eq1 : x 2 = 2 * x 1 - x 0 := by linarith

  have eq2 : x 3 = 3 * x 1 - 2 * x 0 := by
    have eq2a : x 3 - x 2 = x 1 - x 0 := h3
    rw [show x 2 = 2 * x 1 - x 0 by linarith [eq1]] at eq2a
    linarith

  have eq3 : x 4 = 4 * x 1 - 3 * x 0 := by
    have eq3a : x 4 - x 3 = x 1 - x 0 := h4
    rw [show x 3 = 3 * x 1 - 2 * x 0 by linarith [eq2]] at eq3a
    linarith

  have eq4 : x 5 = 5 * x 1 - 4 * x 0 := by
    have eq4a : x 5 - x 4 = x 1 - x 0 := h5
    rw [show x 4 = 4 * x 1 - 3 * x 0 by linarith [eq3]] at eq4a
    linarith

  have eq5 : x 6 = 6 * x 1 - 5 * x 0 := by
    have eq5a : x 6 - x 5 = x 1 - x 0 := h6
    rw [show x 5 = 5 * x 1 - 4 * x 0 by linarith [eq4]] at eq5a
    linarith

  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rw [show x 2 = 2 * x 1 - x 0 by linarith [eq1]] at h3
  rw [show x 3 = 3 * x 1 - 2 * x 0 by linarith [eq2]] at h4
  rw [show x 4 = 4 * x 1 - 3 * x 0 by linarith [eq3]] at h5
  rw [show x 5 = 5 * x 1 - 4 * x 0 by linarith [eq4]] at h6
  rw [show x 6 = 6 * x 1 - 5 * x 0 by linarith [eq5]] at h7

  nlinarith [sq_pos_of_ne_zero ha, sq_nonneg (x 1 - x 0), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c - 51), sq_nonneg (c - 107), sq_nonneg (c - 185), sq_nonneg (c - 285), sq_nonneg (c - 407), sq_nonneg (c - 549), sq_nonneg (c - 717)]