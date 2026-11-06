import Mathlib

theorem algebra_162020 {a g : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 1 + d * (n - 1))
    (hg : ∃ r, ∀ n, g n = g 1 * r ^ (n - 1)) (h : a 1 + g 1 = 0) (h' : a 2 + g 2 = 0)
    (h'' : a 3 + g 3 = 1) (h''' : a 4 + g 4 = 0) :
    a 10 + g 10 = -54 := by

  rcases ha with ⟨d, ha⟩
  rcases hg with ⟨r, hg⟩

  have eq1 : a 2 = a 1 + d := by
    specialize ha 2
    norm_num at ha
    linarith

  have eq2 : a 3 = a 1 + 2 * d := by
    specialize ha 3
    norm_num at ha
    linarith

  have eq3 : a 4 = a 1 + 3 * d := by
    specialize ha 4
    norm_num at ha
    linarith

  have eq4 : g 2 = g 1 * r ^ 1 := by
    specialize hg 2
    simpa using hg

  have eq5 : g 3 = g 1 * r ^ 2 := by
    specialize hg 3
    simpa using hg

  have eq6 : g 4 = g 1 * r ^ 3 := by
    specialize hg 4
    simpa using hg

  rw [eq1, eq4] at h'
  rw [eq2, eq5] at h''
  rw [eq3, eq6] at h'''

  have eq7 : a 1 = -g 1 := by linarith

  have eq8 : d = g 1 * (1 - r) := by
    rw [eq7] at h'
    nlinarith

  have eq9 : g 1 * (r - 1) ^ 2 = 1 := by
    rw [eq7, eq8] at h''
    nlinarith

  have eq10 : g 1 * (r ^ 3 - 3 * r + 2) = 0 := by
    rw [eq7, eq8] at h'''
    nlinarith

  have eq11 : r ^ 3 - 3 * r + 2 = 0 := by
    have h1 : g 1 ≠ 0 := by
      by_contra h2
      rw [h2] at eq9
      nlinarith
    have : r ^ 3 - 3 * r + 2 = 0 := by
      apply (mul_left_inj' h1).mp
      linarith
    assumption

  have eq12 : (r - 1) ^ 2 * (r + 2) = 0 := by
    nlinarith [sq_nonneg (r ^ 2), sq_nonneg ((r + 2) ^ 2), sq_nonneg (r - 1)]

  cases' (mul_eq_zero.mp eq12) with h13 h14

  · -- Case r = 1
    have hr1 : r = 1 := by
      nlinarith

    rw [hr1] at eq9
    nlinarith

  · -- Case r = -2
    have hr2 : r = -2 := by
      linarith

    have eq13 : g 1 = 1 / 9 := by
      rw [hr2] at eq9
      nlinarith

    have eq14 : a 1 = -1 / 9 := by
      linarith [eq7, eq13]

    have eq15 : d = 1 / 3 := by
      rw [eq13, hr2] at eq8
      linarith

    have eq16 : a 10 = a 1 + 9 * d := by
      specialize ha 10
      norm_num at ha
      linarith

    have eq17 : g 10 = g 1 * r ^ 9 := by
      specialize hg 10
      simpa using hg

    rw [eq16, eq17]
    rw [eq14, eq15, eq13, hr2]
    norm_num