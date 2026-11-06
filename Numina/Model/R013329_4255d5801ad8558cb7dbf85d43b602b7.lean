import Mathlib

theorem algebra_123504 {a b : ℤ} (hroots : ∃ x : ℤ, x^2 + a * x + b = 0)
    (hroots' : ∃ x : ℤ, x^2 + a * x + b + 1 = 0) :
    ¬∃ x : ℤ, x^2 + a * x + b + 2 = 0 := by
  rintro ⟨x, hx⟩
  rcases hroots with ⟨r, hr⟩
  rcases hroots' with ⟨t, ht⟩
  have eq1 : r ^ 2 + a * r + b = 0 := by linarith
  have eq2 : t ^ 2 + a * t + b + 1 = 0 := by linarith
  have eq3 : x ^ 2 + a * x + b + 2 = 0 := by linarith
  have eq4 : (r - t) * (r + t + a) = 1 := by
    nlinarith
  have h1 : r - t = 1 ∨ r - t = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one
    exact eq4
  rcases h1 with h5 | h5
  · -- Assume r - t = 1, so r + t + a = 1
    have h5' : r + t + a = 1 := by
      have : (r - t) * (r + t + a) = 1 := eq4
      rw [h5] at this
      linarith
    have h6 : a = -2 * t := by
      nlinarith
    have h7 : b = t ^ 2 - 1 := by
      have hr' : r = t + 1 := by linarith
      rw [hr'] at eq1
      rw [h6] at eq1
      nlinarith
    rw [h6, h7] at hx
    have h9 : (x - t) ^ 2 = -1 := by
      nlinarith
    nlinarith [sq_nonneg (x - t)]
  · -- Assume r - t = -1, so r + t + a = -1
    have h10 : r + t + a = -1 := by
      have : (r - t) * (r + t + a) = 1 := eq4
      rw [h5] at this
      linarith
    have h6 : a = -2 * t := by
      nlinarith
    have h7 : b = t ^ 2 - 1 := by
      have hr' : r = t - 1 := by linarith
      rw [hr'] at eq1
      rw [h6] at eq1
      nlinarith
    rw [h6, h7] at hx
    have h9 : (x - t) ^ 2 = -1 := by
      nlinarith
    nlinarith [sq_nonneg (x - t)]