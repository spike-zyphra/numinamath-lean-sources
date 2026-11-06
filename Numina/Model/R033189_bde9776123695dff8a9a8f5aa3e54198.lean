import Mathlib

theorem algebra_319807 (a : ℕ → ℝ) (h₀ : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (h₁ : 0 < a 0) (h₂ : 0 < a 1) (h₃ : 0 < a 2) (h₄ : 0 < a 3) (h₅ : 0 < a 4)
    (h₆ : 0 < a 5) (h₇ : 0 < a 6) (h₈ : 0 < a 7) (h₉ : 0 < a 8) (h₁₀ : a 0 + a 1 = 3 / 4)
    (h₁₁ : a 2 + a 3 + a 4 + a 5 = 15) :
    a 6 + a 7 + a 8 = 112 := by
  rcases h₀ with ⟨r, hr⟩
  have eq1 : a 1 = a 0 * r ^ 1 := hr 1
  have eq2 : a 2 = a 0 * r ^ 2 := hr 2
  have eq3 : a 3 = a 0 * r ^ 3 := hr 3
  have eq4 : a 4 = a 0 * r ^ 4 := hr 4
  have eq5 : a 5 = a 0 * r ^ 5 := hr 5
  have eq6 : a 6 = a 0 * r ^ 6 := hr 6
  have eq7 : a 7 = a 0 * r ^ 7 := hr 7
  have eq8 : a 8 = a 0 * r ^ 8 := hr 8

  have eq_a1 : a 0 + a 1 = 3 / 4 := h₁₀
  rw [eq1] at eq_a1
  have eq_a2_a5 : a 2 + a 3 + a 4 + a 5 = 15 := h₁₁
  rw [eq2, eq3, eq4, eq5] at eq_a2_a5

  have eq3' : a 0 * (1 + r) = 3 / 4 := by
    nlinarith
  
  have eq4' : a 0 * r ^ 2 * (1 + r + r ^ 2 + r ^ 3) = 15 := by
    nlinarith
  
  have eq5' : 1 + r + r ^ 2 + r ^ 3 = (1 + r) * (1 + r ^ 2) := by
    ring
  
  have eq6' : a 0 * r ^ 2 * (1 + r + r^2 + r ^ 3) = a 0 * r ^ 2 * ( (1 + r) * (1 + r ^ 2) ) := by
    rw [eq5']

  have h2' : a 0 * r ^ 2 * ( (1 + r) * (1 + r ^ 2) ) = r ^ 2 * (a 0 * (1 + r)) * (1 + r ^ 2) := by
    ring_nf

  have h3' : r ^ 2 * (1 + r ^ 2) = 20 := by
    nlinarith [eq3']

  have h4' : r ^ 2 = 4 := by
    nlinarith [sq_nonneg (r ^ 2 - 4), sq_nonneg (r), sq_nonneg (a 0 - 1 / 4)]

  have h5' : r = 2 := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (r)]

  have h6' : a 0 = 1 / 4 := by
    nlinarith [sq_nonneg (r - 2), sq_nonneg (a 0 - 1 / 4), h5']

  have ha6 : a 6 = a 0 * r ^ 6 := eq6
  have ha7 : a 7 = a 0 * r ^ 7 := eq7
  have ha8 : a 8 = a 0 * r ^ 8 := eq8

  rw [ha6, ha7, ha8]

  rw [h6', h5']
  norm_num