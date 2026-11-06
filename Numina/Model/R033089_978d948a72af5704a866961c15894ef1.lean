import Mathlib

theorem algebra_233836 (a : ℕ → ℝ) (h₀ : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h₁ : 0 < a 0) (h₂ : 0 < a 1) (h₃ : 0 < a 2) (h₄ : 0 < a 3) (h₅ : 0 < a 4)
    (h₆ : 0 < a 5) (h₇ : 0 < a 6) (h₈ : 0 < a 7) (h₉ : 0 < a 8) (h₁₀ : a 0 + a 1 = 3 / 4)
    (h₁₁ : a 2 + a 3 + a 4 + a 5 = 15) :
    a 6 + a 7 + a 8 = 112 := by 
  rcases h₀ with ⟨r, hr⟩
  have ha1 : a 1 = a 0 * r ^ 1 := hr 1
  have ha2 : a 2 = a 0 * r ^ 2 := hr 2
  have ha3 : a 3 = a 0 * r ^ 3 := hr 3
  have ha4 : a 4 = a 0 * r ^ 4 := hr 4
  have ha5 : a 5 = a 0 * r ^ 5 := hr 5
  have ha6 : a 6 = a 0 * r ^ 6 := hr 6
  have ha7 : a 7 = a 0 * r ^ 7 := hr 7
  have ha8 : a 8 = a 0 * r ^ 8 := hr 8
  rw [ha1] at h₁₀
  rw [ha2, ha3, ha4, ha5] at h₁₁
  rw [ha6, ha7, ha8]
  have eq1 : a 0 * (1 + r) = 3 / 4 := by
    linarith
  have eq2 : a 0 * r ^ 2 * (1 + r + r ^ 2 + r ^ 3) = 15 := by
    linarith
  have factored : 1 + r + r ^ 2 + r ^ 3 = (1 + r) * (1 + r ^ 2) := by
    ring
  rw [factored] at eq2
  have h_eq : r ^ 2 * (1 + r ^ 2) = 20 := by
    nlinarith [eq1, eq2]
  have h_eq3 : (r ^ 2 + 5) * (r ^ 2 - 4) = 0 := by
    nlinarith [h_eq]
  cases' (mul_eq_zero.mp h_eq3) with h_eq5 h_eq6
  · -- Show that r^2 + 5 = 0 is impossible
    have h_pos : r ^ 2 + 5 > 0 := by
      nlinarith [sq_nonneg r]
    linarith
  · -- Therefore, r^2 - 4 = 0
    have h_eq7 : r ^ 2 = 4 := by
      linarith
    have h_eq8 : r = 2 ∨ r = -2 := by
      have h : r ^ 2 - 4 = 0 := by
        linarith
      have factored : (r - 2) * (r + 2) = 0 := by 
        nlinarith [h]
      cases' (mul_eq_zero.mp factored) with h1 h2
      · -- Case r - 2 = 0
        left
        linarith
      · -- Case r + 2 = 0
        right
        nlinarith
    cases' h_eq8 with h_r2 h_r2
    · -- r = 2
      have eq5 : a 0 = 1 / 4 := by
        rw [show r = 2 by linarith] at eq1
        linarith
      rw [eq5, h_r2]
      norm_num
      <;> nlinarith
    · -- r = -2
      exfalso
      rw [show r = -2 by linarith] at eq1
      nlinarith