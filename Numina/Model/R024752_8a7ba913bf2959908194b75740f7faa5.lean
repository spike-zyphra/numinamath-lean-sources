import Mathlib

theorem algebra_144342 (a : ℕ → ℚ) (h : ∀ n, a n = 2 * a (n - 1) + 1) (ha : a 5 = 7) :
    a 0 = -1 / 2 := by
  have h0 : a 0 = 2 * a 0 + 1 := by
    specialize h 0
    simp at h
    linarith
  have a0_eq : a 0 = -1 := by
    linarith
  have h1 : a 1 = -1 := by
    have eq1 : a 1 = 2 * a 0 + 1 := by
      apply h
    rw [a0_eq] at eq1
    linarith
  have h2 : a 2 = -1 := by
    have eq2 : a 2 = 2 * a 1 + 1 := by
      apply h
    rw [h1] at eq2
    linarith
  have h3 : a 3 = -1 := by
    have eq3 : a 3 = 2 * a 2 + 1 := by
      apply h
    rw [h2] at eq3
    linarith
  have h4 : a 4 = -1 := by
    have eq4 : a 4 = 2 * a 3 + 1 := by
      apply h
    rw [h3] at eq4
    linarith
  have h5 : a 5 = -1 := by
    have eq5 : a 5 = 2 * a 4 + 1 := by
      apply h
    rw [h4] at eq5
    linarith
  exfalso
  linarith [ha, h5]