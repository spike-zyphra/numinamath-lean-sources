import Mathlib

theorem algebra_311927 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha1 : ∀ n, 0 < a n) (h : a 2 * a 4 + 2 * a 3 * a 5 + a 4 * a 6 = 2025) :
    a 3 + a 5 = 45 := by
  rcases ha with ⟨r, hr⟩
  have ha2 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr
  have ha3 : a 3 = a 0 * r ^ 3 := by
    specialize hr 3
    simpa using hr
  have ha4 : a 4 = a 0 * r ^ 4 := by
    specialize hr 4
    simpa using hr
  have ha5 : a 5 = a 0 * r ^ 5 := by
    specialize hr 5
    simpa using hr
  have ha6 : a 6 = a 0 * r ^ 6 := by
    specialize hr 6
    simpa using hr
  rw [ha2, ha3, ha4, ha5, ha6] at h
  have h1 : (a 0 * r ^ 3 + a 0 * r ^ 5) ^ 2 = 2025 := by
    nlinarith
  have h2 : 0 < a 3 := by
    apply ha1 3
  have h3 : 0 < a 5 := by
    apply ha1 5
  have h4 : a 3 + a 5 > 0 := by
    nlinarith [h2, h3]
  have h6 : (a 0 * r ^ 3 + a 0 * r ^ 5) = 45 := by
    nlinarith [h1, sq_nonneg (a 0 * r ^ 3 + a 0 * r ^ 5 - 45), sq_nonneg (a 0 * r ^ 3 + a 0 * r ^ 5 + 45), sq_pos_of_pos (ha1 0), sq_pos_of_pos (ha1 1), sq_pos_of_pos (ha1 2), sq_pos_of_pos (ha1 3), sq_pos_of_pos (ha1 4), sq_pos_of_pos (ha1 5), sq_pos_of_pos (ha1 6)]
  nlinarith [ha3, ha5, h6]