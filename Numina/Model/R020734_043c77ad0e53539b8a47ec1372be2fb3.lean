import Mathlib

theorem inequalities_182955 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x / (y + z) + y / (x + z) + z / (x + y) ≤ x * Real.sqrt x / 2 + y * Real.sqrt y / 2 + z * Real.sqrt z / 2 := by

  have h1 : x / (y + z) ≤ x * Real.sqrt x / 2 := by
    have h1 : y + z ≥ 2 * Real.sqrt (y * z):= by
      have h1 : Real.sqrt (y * z) = Real.sqrt y * Real.sqrt z := by
        rw [Real.sqrt_mul]
        all_goals linarith
      nlinarith [sq_nonneg (y - z), sq_nonneg (Real.sqrt y - Real.sqrt z),
        Real.sq_sqrt (show 0 ≤ y by linarith), Real.sq_sqrt (show 0 ≤ z by linarith),
        Real.sqrt_nonneg y, Real.sqrt_nonneg z]

    have h2 : Real.sqrt (y * z) = Real.sqrt (1 / x):= by
      have h2 : y * z = 1 / x := by
        have h2 : x * y * z = 1 := hxyz
        field_simp
        nlinarith
      rw [h2]

    have h3 : Real.sqrt (1 / x) = Real.sqrt 1 / Real.sqrt x := by
      field_simp [Real.sqrt_mul]

    rw [h3] at h2

    have h4 : Real.sqrt 1 = 1 := by
      rw [Real.sqrt_eq_cases]
      norm_num

    rw [h4] at h2

    have h5 : Real.sqrt (y * z) = 1 / Real.sqrt x := by
      linarith [h2]

    have h6 : y + z ≥ 2 * (1 / Real.sqrt x):= by
      linarith [h1, h5]

    have h7 : x / (y + z) ≤ x / (2 * (1 / Real.sqrt x)) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h6]

    have h8 : x / (2 * (1 / Real.sqrt x)) = x * Real.sqrt x / 2 := by
      field_simp
      <;> ring_nf <;> rw [Real.sq_sqrt (show 0 ≤ x by positivity)]
        <;> nlinarith

    linarith [h7, h8]

  have h2 : y / (x + z) ≤ y * Real.sqrt y / 2 := by
    have h1 : x + z ≥ 2 * Real.sqrt (x * z):= by
      have h1 : Real.sqrt (x * z) = Real.sqrt x * Real.sqrt z := by
        rw [Real.sqrt_mul]
        all_goals linarith
      nlinarith [sq_nonneg (x - z), sq_nonneg (Real.sqrt x - Real.sqrt z),
        Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ z by linarith),
        Real.sqrt_nonneg x, Real.sqrt_nonneg z]

    have h2 : Real.sqrt (x * z) = Real.sqrt (1 / y):= by
      have h2 : x * z = 1 / y := by
        have h2 : x * y * z = 1 := hxyz
        field_simp
        nlinarith
      rw [h2]

    have h3 : Real.sqrt (1 / y) = Real.sqrt 1 / Real.sqrt y := by
      field_simp [Real.sqrt_mul]

    rw [h3] at h2

    have h4 : Real.sqrt 1 = 1 := by
      rw [Real.sqrt_eq_cases]
      norm_num

    rw [h4] at h2

    have h5 : Real.sqrt (x * z) = 1 / Real.sqrt y := by
      linarith [h2]

    have h6 : x + z ≥ 2 * (1 / Real.sqrt y):= by
      linarith [h1, h5]

    have h7 : y / (x + z) ≤ y / (2 * (1 / Real.sqrt y)) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h6]

    have h8 : y / (2 * (1 / Real.sqrt y)) = y * Real.sqrt y / 2 := by
      field_simp
      <;> ring_nf <;> rw [Real.sq_sqrt (show 0 ≤ y by positivity)]
        <;> nlinarith

    linarith [h7, h8]

  have h3 : z / (x + y) ≤ z * Real.sqrt z / 2 := by
    have h1 : x + y ≥ 2 * Real.sqrt (x * y):= by
      have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
        rw [Real.sqrt_mul]
        all_goals linarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (Real.sqrt x - Real.sqrt y),
        Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith),
        Real.sqrt_nonneg x, Real.sqrt_nonneg y]

    have h2 : Real.sqrt (x * y) = Real.sqrt (1 / z):= by
      have h2 : x * y = 1 / z := by
        have h2 : x * y * z = 1 := hxyz
        field_simp
        nlinarith
      rw [h2]

    have h3 : Real.sqrt (1 / z) = Real.sqrt 1 / Real.sqrt z := by
      field_simp [Real.sqrt_mul]

    rw [h3] at h2

    have h4 : Real.sqrt 1 = 1 := by
      rw [Real.sqrt_eq_cases]
      norm_num

    rw [h4] at h2

    have h5 : Real.sqrt (x * y) = 1 / Real.sqrt z := by
      linarith [h2]

    have h6 : x + y ≥ 2 * (1 / Real.sqrt z):= by
      linarith [h1, h5]

    have h7 : z / (x + y) ≤ z / (2 * (1 / Real.sqrt z)) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h6]

    have h8 : z / (2 * (1 / Real.sqrt z)) = z * Real.sqrt z / 2 := by
      field_simp
      <;> ring_nf <;> rw [Real.sq_sqrt (show 0 ≤ z by positivity)]
        <;> nlinarith

    linarith [h7, h8]

  linarith [h1, h2, h3]