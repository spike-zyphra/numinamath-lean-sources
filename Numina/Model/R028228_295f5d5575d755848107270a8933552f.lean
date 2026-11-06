import Mathlib

theorem algebra_11431 (a : ℕ → ℝ) (h : ∃ r, ∀ n, a n = a 0 * r ^ n) (ha : ∀ n, 0 < a n)
    (h1 : a 6 + a 5 + a 4 - a 3 - a 2 - a 1 = 49) :
    a 9 + a 8 + a 7 ≥ 196 := by
  rcases h with ⟨r, hr⟩
  have ha0_pos : 0 < a 0 := by
    have h2 := ha 0
    simpa using h2
  have eq1 : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    simpa using hr
  have eq2 : a 2 = a 0 * r ^ 2 := by
    specialize hr 2
    simpa using hr
  have eq3 : a 3 = a 0 * r ^ 3 := by
    specialize hr 3
    simpa using hr
  have eq4 : a 4 = a 0 * r ^ 4 := by
    specialize hr 4
    simpa using hr
  have eq5 : a 5 = a 0 * r ^ 5 := by
    specialize hr 5
    simpa using hr
  have eq6 : a 6 = a 0 * r ^ 6 := by
    specialize hr 6
    simpa using hr
  have eq7 : a 7 = a 0 * r ^ 7 := by
    specialize hr 7
    simpa using hr
  have eq8 : a 8 = a 0 * r ^ 8 := by
    specialize hr 8
    simpa using hr
  have eq9 : a 9 = a 0 * r ^ 9 := by
    specialize hr 9
    simpa using hr
  rw [eq6, eq5, eq4, eq3, eq2, eq1] at h1
  rw [eq9, eq8, eq7] at *
  have h3 : 0 < r := by
    nlinarith [ha0_pos, show 0 < a 0 * r ^ 1 by nlinarith [ha 1], sq_nonneg (r), sq_nonneg (a 0), sq_nonneg (r - 1)]
  have h30 : 1 < r ^ 3 := by
    by_contra h4
    push_neg at h4
    have h31 : r ^ 3 ≤ 1 := by linarith
    have h32 : a 0 * r * (r ^ 3 - 1) * (r ^ 2 + r + 1) ≤ 0 := by
      have h33 : r ^ 3 - 1 ≤ 0 := by nlinarith
      have h34 : r ^ 2 + r + 1 > 0 := by
        nlinarith [sq_nonneg (r + 1/2), h3]
      have h35 : a 0 * r > 0 := mul_pos ha0_pos h3
      have h36 : (r ^ 3 - 1) * (r ^ 2 + r + 1) ≤ 0 := by
        nlinarith
      nlinarith
    nlinarith [show a 0 * r * (r ^ 3 - 1) * (r ^ 2 + r + 1) = 49 by linarith [h1], h32]
  have h22 : a 0 * r ^ 7 * (r ^ 2 + r + 1) ≥ 196 := by
    have h23 : a 0 * r * (r ^ 3 - 1) * (r ^ 2 + r + 1) = 49 := by
      linarith
    have h24 : a 0 * r ^ 7 * (r ^ 2 + r + 1) = r^6 * (a 0 * r * (r ^ 2 + r + 1)) := by
      ring
    rw [h24]
    have h26 : r^6 * (a 0 * r * (r ^ 2 + r + 1)) ≥ 196 := by
      have eq27 : a 0 * r * (r ^ 2 + r + 1) = 49 / (r ^ 3 - 1) := by
        have h28 : r ^ 3 - 1 ≠ 0 := by nlinarith
        field_simp
        nlinarith [h23]
      have eq28 : r ^ 6 * (a 0 * r * (r ^ 2 + r + 1)) = 49 * (r ^ 6 / (r ^ 3 - 1)) := by
        rw [eq27]
        field_simp [(show r ^ 3 - 1 ≠ 0 by nlinarith)]
        all_goals nlinarith
      rw [eq28]
      have h29 : r ^ 6 / (r ^ 3 - 1) ≥ 4 := by
        have h31 : r ^ 3 - 1 > 0 := by nlinarith
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (r ^ 3 - 2), sq_nonneg (r ^ 3 - 1), sq_nonneg (r ^ 3), sq_nonneg (r^3 - 2), sq_nonneg (r^3 - 1)]
      have h30 : 49 * (r ^ 6 / (r ^ 3 - 1)) ≥ 196 := by
        nlinarith [h29]
      linarith
    linarith
  nlinarith