import Mathlib

theorem algebra_319114 {a : ℕ → ℝ} {q : ℝ} (ha : ∀ n, a n = a 0 * q ^ n)
    (h5 : a 5 = 2 * (a 1 + a 2 + a 3 + a 4) + 3) (h6 : a 6 = 2 * (a 1 + a 2 + a 3 + a 4 + a 5) + 3) :
    q = 3 := by

  have eq1 : a 5 = a 0 * q ^ 5 := by
    specialize ha 5
    simpa using ha
  have eq2 : a 6 = a 0 * q ^ 6 := by
    specialize ha 6
    simpa using ha
  have eq3 : a 1 = a 0 * q ^ 1 := by
    specialize ha 1
    simpa using ha
  have eq4 : a 2 = a 0 * q ^ 2 := by
    specialize ha 2
    simpa using ha
  have eq5 : a 3 = a 0 * q ^ 3 := by
    specialize ha 3
    simpa using ha
  have eq6 : a 4 = a 0 * q ^ 4 := by
    specialize ha 4
    simpa using ha

  rw [eq1] at h5
  rw [eq2] at h6

  rw [eq3, eq4, eq5, eq6] at h5
  rw [eq3, eq4, eq5, eq6, eq1] at h6

  have eq_sub : a 0 * q ^ 6 - (a 0 * q ^ 5) = 2 * (a 0 * q ^ 5) := by
    linarith

  have h7 : a 0 * q ^ 5 * (q - 1) = 2 * (a 0 * q ^ 5) := by
    linarith [eq_sub]

  have h8 : a 0 * q ^ 5 * (q - 3) = 0 := by
    linarith [h7]

  cases' (mul_eq_zero.mp h8) with h9 h10

  · -- Assume a_0 * q^5 = 0
    cases' (mul_eq_zero.mp h9) with h11 h12
    · -- Assume a_0 = 0
      have ha0 : a 0 = 0 := by linarith
      rw [ha0] at h5
      nlinarith
    · -- Assume q^5 = 0, so q = 0
      have h0 : q ^ 5 = 0 := by
        linarith
      have hq0 : q = 0 := by
        have h2 : q ^ 5 = 0 := h0
        have h3 : q ^ 5 = 0 := h2
        simpa using h2
      rw [hq0] at h5
      nlinarith

  · -- Assume q - 3 = 0, so q = 3
    linarith