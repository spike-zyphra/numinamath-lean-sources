import Mathlib

theorem algebra_162142 {a : ℕ → ℝ} (h : ∃ r, ∀ n, a n = a 0 * r ^ n) (ha : ∀ n, 0 < a n)
    (h1 : a 2 * a 4 + 2 * a 3 * a 5 + a 4 * a 6 = 2025) : a 3 + a 5 = 45 := by
  rcases h with ⟨r, hr⟩
  have ha2 : 0 < a 2 := ha 2
  have ha3 : 0 < a 3 := ha 3
  have ha4 : 0 < a 4 := ha 4
  have ha5 : 0 < a 5 := ha 5
  have ha6 : 0 < a 6 := ha 6

  have eq_a2 : a 2 = a 0 * r^2 := by
    specialize hr 2
    simpa using hr
  have eq_a3 : a 3 = a 0 * r^3 := by
    specialize hr 3
    simpa using hr
  have eq_a4 : a 4 = a 0 * r^4 := by
    specialize hr 4
    simpa using hr
  have eq_a5 : a 5 = a 0 * r^5 := by
    specialize hr 5
    simpa using hr
  have eq_a6 : a 6 = a 0 * r^6 := by
    specialize hr 6
    simpa using hr
  
  rw [eq_a2, eq_a3, eq_a4, eq_a5, eq_a6] at h1
  
  have h2 : 0 < r := by
    have h0 : 0 < a 1 := ha 1
    have h1_eq : a 1 = a 0 * r^1 := by
      specialize hr 1
      simpa using hr
    rw [h1_eq] at h0
    have hc : a 0 > 0 := by linarith [ha 0]
    nlinarith [sq_nonneg r, hc]

  have h5 : a 0 * r^3 * (1 + r^2) = 45 := by
    have h2_pos : a 0 * r^3 * (1 + r^2) > 0 := by
      apply mul_pos
      apply mul_pos
      · linarith [ha 0]
      · -- r^3 > 0
        nlinarith [show r^2 >= 0 by nlinarith, show r > 0 by nlinarith [sq_nonneg r, ha 0, ha 1]]
      · -- 1 + r^2 > 0
        nlinarith [show r^2 >= 0 by nlinarith, show r > 0 by nlinarith [sq_nonneg r, ha 0, ha 1]]
    have h4 : (a 0 * r^3 * (1 + r^2))^2 = 2025 := by
      nlinarith
    have h6 : a 0 * r^3 * (1 + r^2) = 45 := by
      nlinarith [h2_pos, sq_nonneg (a 0 * r^3 * (1 + r^2) - 45), sq_nonneg (a 0 * r^3 * (1 + r^2) + 45)]
    exact h6
  
  have h7 : a 3 + a 5 = 45 := by
    rw [eq_a3, eq_a5]
    nlinarith [h5, h2]

  exact h7