import Mathlib

theorem algebra_12379 (a : ℕ → ℝ) (h₀ : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h₁ : 0 < a 0) (h₂ : 0 < a 1) (h₃ : 0 < a 2) (h₄ : 0 < a 3)
    (h₅ : 0 < a 4) (h₆ : 0 < a 5) (h₇ : 0 < a 6) (h₈ : 0 < a 7)
    (h₉ : 0 < a 8) (h₁₀ : a 0 + a 1 = 3 / 4) (h₁₁ : a 2 + a 3 + a 4 + a 5 = 15) :
    a 6 + a 7 + a 8 = 112 := by
  rcases h₀ with ⟨r, hr⟩
  have ha1 : a 1 = a 0 * r ^ 1 := by
    specialize hr 1
    simpa using hr
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
  have ha7 : a 7 = a 0 * r ^ 7 := by
    specialize hr 7
    simpa using hr
  have ha8 : a 8 = a 0 * r ^ 8 := by
    specialize hr 8
    simpa using hr
  have eq1 : a 0 * (1 + r) = 3 / 4 := by
    have h : a 0 + a 1 = 3 / 4 := h₁₀
    rw [ha1] at h 
    linarith
  have eq2 : a 0 * r ^ 2 * (1 + r + r ^ 2 + r ^ 3) = 15 := by
    have h : a 2 + a 3 + a 4 + a 5 = 15 := h₁₁
    rw [ha2, ha3, ha4, ha5] at h
    linarith
  have eq3 : r ^ 2 + r ^ 4 = 20 := by
    have h : a 0 * (1 + r) = 3 / 4 := eq1
    have h2 : a 0 * r ^ 2 * (1 + r + r ^ 2 + r ^ 3) = 15 := eq2
    have h3 : 1 + r + r ^ 2 + r ^ 3 = (1 + r) * (1 + r ^ 2) := by 
      ring
    have h4 : a 0 * r ^ 2 * (1 + r + r ^ 2 + r ^ 3) = 
        a 0 * r ^ 2 * ((1 + r) * (1 + r ^ 2)) := by 
      rw [h3]
    have h5 : a 0 * r ^ 2 * ((1 + r) * (1 + r ^ 2)) = 
      (a 0 * (1 + r)) * (r ^ 2 * (1 + r ^ 2)) := by 
        ring
    rw [h4, h5] at eq2
    rw [show a 0 * (1 + r) = 3 / 4 by linarith [eq1] ] at eq2
    nlinarith 
  have eq4 : r ^ 2 = 4 := by
    nlinarith [sq_nonneg (r ^ 2 - 4), sq_nonneg (r ^ 2 + 4), sq_nonneg (r * 0), sq_nonneg (0 : ℝ)]
  have eq5 : r = 2 := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (r + 2), sq_nonneg (0 : ℝ), sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num)]
  have eq6 : a 0 = 1 / 4 := by 
    rw [eq5] at eq1
    linarith
  have eq7 : a 6 + a 7 + a 8 = 112 := by 
    rw [ha6, ha7, ha8]
    rw [eq5, eq6]
    norm_num
  exact eq7