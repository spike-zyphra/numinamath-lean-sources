import Mathlib

theorem algebra_609947 (a : ℕ → ℚ) (b : ℕ → ℚ)
    (ha : ∃ c d : ℚ, c ≠ 0 ∧ d ≠ 0 ∧ ∀ n : ℕ, (a n) = c + n*d) 
    (hb : ∃ e r : ℚ, e ≠ 0 ∧ r ≠ 0 ∧ ∀ n : ℕ, (b n) = e * r^n) 
    (h0 : (a 0) * (b 0) = 20) 
    (h1 : (a 1) * (b 1) = 19)
    (h2 : (a 2) * (b 2) = 14)
  : (a 3) * (b 3) ≤ 37 / 4 := by

  rcases ha with ⟨c, d, hc, hd, had⟩
  rcases hb with ⟨e, r, he, hr, hbe⟩

  have eq1 : a 0 = c := by 
    specialize had 0
    norm_num at had ⊢
    linarith

  have eq2 : a 1 = c + d := by
    specialize had 1
    norm_num at had ⊢
    linarith

  have eq3 : a 2 = c + 2 * d := by 
    specialize had 2
    norm_num at had ⊢
    linarith

  have eq4 : a 3 = c + 3 * d := by 
    specialize had 3
    norm_num at had ⊢
    linarith

  have eq5 : b 0 = e := by 
    specialize hbe 0
    simpa using hbe

  have eq6 : b 1 = e * r := by 
      specialize hbe 1
      simpa using hbe

  have eq7 : b 2 = e * r^2 := by 
      specialize hbe 2
      simpa using hbe

  have eq8 : b 3 = e * r^3 := by 
      specialize hbe 3
      simpa using hbe

  rw [eq1, eq5] at h0
  rw [eq2, eq6] at h1
  rw [eq3, eq7] at h2

  have h3 : (c + 3 * d) * (e * r^3) ≤ 37 / 4 := by 
    nlinarith [sq_nonneg (d * r - 1 / 2), sq_nonneg (c - 10), sq_nonneg (e * r - 2), sq_nonneg (d - 1 / 2), sq_nonneg (c * r - 10), sq_nonneg (e - 2), sq_pos_of_ne_zero hd, sq_pos_of_ne_zero he, sq_nonneg (r - 1 / 2), sq_nonneg (d - 1 / 2), mul_ne_zero he hd]

  have h4 : (a 3) * (b 3) = (c + 3 * d) * (e * r^3) := by 
    rw [eq4, eq8]

  linarith [h3, h4]