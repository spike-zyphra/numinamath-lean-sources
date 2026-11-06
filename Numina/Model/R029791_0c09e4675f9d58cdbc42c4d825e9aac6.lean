import Mathlib

theorem algebra_11966 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha9 : a 9 = 13) (ha13 : a 13 = 1) :
    Real.logb (a 1) 13 = 1 / 3 := by
  rcases ha with ⟨r, hr⟩
  have h9 : a 9 = a 0 * r ^ 9 := by
    specialize hr 9
    simpa using hr
  rw [h9] at ha9
  have h13 : a 13 = a 0 * r ^ 13 := by
    specialize hr 13
    simpa using hr
  rw [h13] at ha13
  have h1 : r ^ 4 = 1 / 13 := by
    have h2 : a 0 * r ^ 13 = (a 0 * r ^ 9) * r ^ 4 := by ring
    rw [h2] at ha13
    rw [ha9] at ha13
    nlinarith
  have h2 : a 1 = a 0 * r := by
    have h3 : a 1 = a 0 * r ^ 1 := by
      specialize hr 1
      simpa using hr
    ring_nf at h3 ⊢
    linarith
  have h3 : a 1 = 13 ^ 3 := by
    have h4 : a 0 * r ^ 9 = 13 := by
      linarith
    have h5 : r ≠ 0 := by
      by_contra h
      rw [h] at h1
      nlinarith
    have h6 : a 1 * r ^ 8 = 13 := by
      have h11 : a 0 * r ^ 9 = 13 := by
        linarith
      have h9' : a 0 * r ^ 9 = (a 1) * r ^ 8 := by
        have h10 : a 1 = a 0 * r := by
          linarith [h2]
        rw [h10]
        ring_nf
      linarith
    have h7 : r ^ 8 = 1 / 169 := by
      calc
        r ^ 8 = (r ^ 4) ^ 2 := by ring
        _ = (1 / 13) ^ 2 := by rw [h1]
        _ = 1 / 169 := by norm_num
    rw [h7] at h6
    have h10 : a 1 = 13 * 169 := by
      nlinarith
    have h11 : a 1 = 13 ^ 3 := by
      nlinarith
    exact h11
  rw [h3]
  have h10 : Real.logb (13 ^ 3) 13 = 1 / 3 := by
    rw [Real.logb]
    have h11 : Real.log (13 ^ 3 : ℝ) = 3 * Real.log (13 : ℝ) := by
      simp [Real.log_pow]
    rw [h11]
    have h12 : Real.log (13 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals
        norm_num
    field_simp [h12]
    all_goals
      nlinarith
  linarith