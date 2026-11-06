import Mathlib

theorem algebra_12252 {a r : ℝ} (hr : r ≠ 0) (h1 : ∑ i ∈ Finset.range 2011, a * r ^ i = 200)
    (h2 : ∑ i ∈ Finset.range 4022, a * r ^ i = 380) :
    ∑ i ∈ Finset.range 6033, a * r ^ i = 542 := by
  have h3 : ∀ (n : ℕ), ∑ i ∈ Finset.range n, a * r ^ i = a * (1 - r ^ n) / (1 - r) := by
    intro n
    induction n with
    | zero =>
      simp [Finset.sum_range_zero]
      <;> field_simp [(show (1 - r : ℝ) ≠ 0 by
          by_contra h
          have : r = 1 := by linarith
          rw [this] at h1 h2
          norm_num [Finset.sum_range_succ] at h1 h2
          all_goals linarith
          )
      ]
      <;> ring_nf <;> field_simp <;> ring
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [(show (1 - r : ℝ) ≠ 0 by
        by_contra h
        have : r = 1 := by linarith
        rw [this] at h1 h2
        norm_num [Finset.sum_range_succ] at h1 h2
        all_goals linarith
      )
      ]
      <;> ring_nf
      <;> field_simp <;> ring
      <;> norm_num
  -- Substitute h1 using h3
  have h4 := h3 2011
  have eq1 : a * (1 - r ^ 2011) / (1 - r) = 200 := by
    linarith
  -- Substitute h2 using h3
  have h5 := h3 4022
  have eq2 : a * (1 - r ^ 4022) / (1 - r) = 380 := by
    linarith
  have eq3 : r ^ 4022 = (r ^ 2011) ^ 2 := by
    ring
  have h5' : a * (1 - r ^ 4022) / (1 - r) = 380 := by
    linarith
  have eq5 : a * (1 - r ^ 4022) / (1 - r) = a * (1 - (r ^ 2011) ^ 2) / (1 - r) := by
    rw [eq3]
  have h6 : a * (1 - (r ^ 2011) ^ 2) / (1 - r) = 380 := by
    linarith
  have h7 : (1 - (r ^ 2011) ^ 2 : ℝ) = (1 - r ^ 2011) * (1 + r ^ 2011) := by
    ring_nf
  have h7' : a * (1 - (r ^ 2011) ^ 2) / (1 - r) = a * ((1 - r ^ 2011) * (1 + r ^ 2011)) / (1 - r) := by
    rw [h7]
    all_goals ring_nf
  have h8 : a * ((1 - r ^ 2011) * (1 + r ^ 2011)) / (1 - r) = 380 := by
    linarith [h7', h6]

  -- Substitute linarith step is correct here
  have h5'' : a * (1 - r ^ 2011) * (1 + r ^ 2011) = 380 * (1 - r) := by
    have h6' : a * ((1 - r ^ 2011) * (1 + r ^ 2011)) / (1 - r) = 380 := by
      linarith
    have h_eq : (1 - r : ℝ) ≠ 0 := by
      by_contra h_zero
      have r1 : r = 1 := by
        linarith
      rw [r1] at h1 h2
      norm_num [Finset.sum_range_succ] at h1 h2
      all_goals linarith
    have eq : a * ((1 - r ^ 2011) * (1 + r ^ 2011)) = 380 * (1 - r) := by
      field_simp [h_eq] at h6' ⊢
      <;> nlinarith [sq_nonneg (1 - r ^ 2011), sq_nonneg (a), sq_nonneg (r - 1)]
    linarith

  have h5''' : a * (1 - r ^ 2011) / (1 - r) * (1 + r ^ 2011) = 380 := by
    have eq : a * (1 - r ^ 2011) / (1 - r) * (1 + r ^ 2011) = (a * (1 - r ^ 2011) * (1 + r ^ 2011)) / (1 - r) := by
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    rw [eq]
    have h_eq : (1 - r : ℝ) ≠ 0 := by
      by_contra h_zero
      have r1 : r = 1 := by
        linarith
      rw [r1] at h1 h2
      norm_num [Finset.sum_range_succ] at h1 h2
      all_goals linarith
    have eq2 : a * (1 - r ^ 2011) * (1 + r ^ 2011) = 380 * (1 - r) := by
      linarith
    rw [eq2]
    field_simp [h_eq]
    <;> ring_nf
    all_goals try { tauto } <;> tauto

  have h5'''' : 200 * (1 + r ^ 2011) = 380 := by
    rw [eq1] at h5'''
    linarith

  have h5''''' : r ^ 2011 = 9 / 10 := by
    nlinarith

  -- Now need to compute sum from 0 to 6032.
  have h7 := h3 6033
  have eq4 : ∑ i ∈ Finset.range 6033, a * r ^ i = a * (1 - r ^ 6033) / (1 - r) := by
    linarith [h7]

  have eq5 : r ^ 6033 = (r ^ 2011) ^ 3 := by
    ring

  have eq6 : a * (1 - r ^ 6033) / (1 - r) = a * (1 - (r ^ 2011) ^ 3) / (1 - r) := by
    rw [eq5]
 
  -- Substitute our r^ 2011 value
  have eq7 : a * (1 - (r ^ 2011) ^ 3) / (1 - r) = a * (1 - r ^ 2011) / (1 - r) * (1 + r ^ 2011 + (r ^ 2011) ^ 2) := by
    have h8 : 1 - (r ^ 2011) ^ 3 = (1 - r ^ 2011) * (1 + r ^ 2011 + (r ^ 2011) ^ 2) := by
      ring_nf
    rw [h8]
    field_simp [(show (1 - r : ℝ) ≠ 0 by
      by_contra h_eq
      have r1 : r = 1 := by
        linarith
      rw [r1] at h1 h2
      norm_num [Finset.sum_range_succ] at h1 h2
      all_goals linarith
    )
    ]
    <;> ring_nf <;> field_simp

  have eq8 : a * (1 - r ^ 2011) / (1 - r) = 200 := by
    linarith
  have eq9 : (1 + r ^ 2011 + (r ^ 2011) ^ 2 : ℝ) = (1 + (9/10) + (9/10:ℝ) ^ 2 : ℝ) := by
    rw [show r ^ 2011 = (9/10 : ℝ) by linarith [h5''''']]
  have h31 : (1 + r ^ 2011 + (r ^ 2011) ^ 2 : ℝ) = 2.71 := by
    rw [show r ^ 2011 = (9/10 : ℝ) by linarith [h5''''']]
    norm_num
  
  have eq10 : a * (1 - r ^ 2011) / (1 - r) * (1 + r ^ 2011 + (r ^ 2011) ^ 2) = 542 := by
    have h_eq1 : a * (1 - r ^ 2011) / (1 - r) = 200 := by
      linarith
    have h_eq2 : (1 + r ^ 2011 + (r ^ 2011) ^ 2 : ℝ) = 2.71 := by
      rw [show r ^ 2011 = (9/10 : ℝ) by linarith [h5''''']]
      norm_num
    rw [h_eq1, h_eq2]
    all_goals norm_num
    <;> nlinarith [sq_nonneg (a - (a / (2/1))), sq_nonneg (r ^ 2011 - 1), sq_nonneg (r - 1), sq_nonneg (1 - r)]
  -- We now connect our computed expression to the final answer
  have eq11 : a * (1 - r ^ 6033) / (1 - r) = 542 := by
    rw [eq6]
    rw [eq7]
    linarith [eq10]

  -- Final conclusion
  linarith [eq11, eq4]