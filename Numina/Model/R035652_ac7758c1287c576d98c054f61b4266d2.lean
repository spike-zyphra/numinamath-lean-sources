import Mathlib

theorem algebra_183995 (a b c d e f : ℝ)
    (h₀ : (a + b + c + d + e) / 5 = 24.5)
    (h₁ : (a + b + c + d + e + f) / 6 = 27) :
    f = 39.5 := by

  have h2 : a + b + c + d + e = 122.5 := by
    have eq1 : (a + b + c + d + e) / 5 = 24.5 := h₀
    have eq2 : a + b + c + d + e = 5 * 24.5 := by
      linarith
    rw [eq2]
    norm_num

  have h3 : a + b + c + d + e + f = 162 := by
    have eq3 : (a + b + c + d + e + f) / 6 = 27 := h₁
    have eq4 : a + b + c + d + e + f = 6 * 27 := by 
      linarith
    rw [eq4]
    norm_num

  have eq5 : f = 39.5 := by
    linarith [h2, h3]

  exact_mod_cast eq5