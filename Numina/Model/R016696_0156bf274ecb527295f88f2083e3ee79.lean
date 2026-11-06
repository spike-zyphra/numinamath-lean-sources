import Mathlib

theorem algebra_282975 {a g : ℕ → ℤ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hg : ∃ r, ∀ n, g n = g 0 * r ^ n) (h : a 0 + g 0 = 27 ∧ a 1 + g 1 = 27 ∧
    a 2 + g 2 = 39 ∧ a 3 + g 3 = 87) :
    a 0 = 24 ∧ a 1 = 18 ∧ a 2 = 12 ∧ a 3 = 6 ∧ g 0 = 3 ∧ g 1 = 9 ∧ g 2 = 27 ∧ g 3 = 81 := by
  rcases h with ⟨h1, h2, h3, h4⟩
  rcases ha with ⟨d, had⟩
  rcases hg with ⟨r, hg⟩

  have eq2 : a 1 = a 0 + d := by
    specialize had 1
    norm_num at had
    linarith

  have eq3 : a 2 = a 0 + 2 * d := by
    specialize had 2
    norm_num at had
    linarith

  have eq4 : a 3 = a 0 + 3 * d := by
    specialize had 3
    norm_num at had
    linarith

  have eq5 : g 1 = g 0 * r ^ 1 := by
    specialize hg 1
    simpa using hg

  have eq6 : g 2 = g 0 * r ^ 2 := by
    specialize hg 2
    simpa using hg

  have eq7 : g 3 = g 0 * r ^ 3 := by
    specialize hg 3
    simpa using hg

  rw [eq2] at h2
  rw [eq3] at h3
  rw [eq4] at h4
  rw [eq5] at h2
  rw [eq6] at h3
  rw [eq7] at h4

  have h5 : r = 3 := by
    have eq1 := h1
    have eq2 := h2
    have eq3 := h3
    have eq4 := h4
    -- Solving the system of equations
    -- 1. a0 + g0 = 27
    -- 2. a0 + d + g0 * r = 27
    -- 3. a0 + 2 * d + g0 * r^2 = 39
    -- 4. a0 + 3 * d + g0 * r^3 = 87
    have h6 : r = 3 := by
      -- Subtracting eq2 - eq1: d + g0 * (r - 1) = 0
      -- Subtracting eq3 - eq2: d + g0 * (r^2 - r) = 12
      -- Subtracting eq4 - eq3: d + g0 * (r^3 - r^2) = 48
      -- From first two subtractions: g0 * (r - 1)^2 = 12
      -- From last two subtractions: g0 * r * (r - 1)^2 = 36
      -- Dividing: r = 3
      nlinarith [ sq_nonneg ((r : ℤ) - 3), sq_nonneg ((g 0 : ℤ) - 3 : ℤ), sq_nonneg ((d : ℤ) + 6 : ℤ), sq_nonneg ((a 0 : ℤ) - 24 : ℤ) ]
    exact h6

  have h6 : g 0 = 3 := by
    rw [h5] at h2 h3 h4
    nlinarith [ sq_nonneg ((a 0 : ℤ) - 24 : ℤ), sq_nonneg ((d : ℤ) + 6 : ℤ) ]

  have h7 : a 0 = 24 := by
    nlinarith

  have h8 : d = -6 := by
    rw [h6, h7, h5] at h2
    nlinarith

  have ha1 : a 1 = 18 := by
    linarith [ eq2, h7, h8 ]

  have ha2 : a 2 = 12 := by
    linarith [ eq3, h7, h8 ]

  have ha3 : a 3 = 6 := by
    linarith [ eq4, h7, h8 ]

  have hg1 : g 1 = 9 := by
    rw [eq5, h6, h5]
    norm_num

  have hg2 : g 2 = 27 := by
    rw [eq6, h6, h5]
    norm_num

  have hg3 : g 3 = 81 := by
    rw [eq7, h6, h5]
    norm_num

  exact ⟨h7, ha1, ha2, ha3, h6, hg1, hg2, hg3⟩