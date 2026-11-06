import Mathlib

theorem algebra_194269 (a : ℝ) (h : ∃ x : Fin 2 → ℝ, ∀ i, x i ^ 4 + a * x i ^ 2 - 2017 = 0 ∧
    x 0 ^ 2 + x 1 ^ 2 = 4) :
    a = 1006.5 := by
  rcases h with ⟨x, hx⟩
  have h0 := hx 0
  have h1 := hx 1
  have eq0 := h0.1
  have eq1 := h1.1
  have eq_sum : x 0 ^ 2 + x 1 ^ 2 = 4 := by
    linarith [h0.2, h1.2]
  have eq_eq0' : (x 0 ^ 2) ^ 2 + a * (x 0 ^ 2) - 2017 = 0 := by
    nlinarith
  have eq_eq1' : (x 1 ^ 2) ^ 2 + a * (x 1 ^ 2) - 2017 = 0 := by
    nlinarith
  have eq5 : (x 0 ^ 2 - x 1 ^ 2) * (4 + a) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq5) with eq6 eq7
  · -- Case where x 0 ^ 2 = x 1 ^ 2
    have eq8 : x 0 ^ 2 = x 1 ^ 2 := by linarith
    have eq9 : x 0 ^ 2 = 2 := by
      nlinarith
    have eq9' : (x 0 ^ 2) ^ 2 + a * (x 0 ^ 2) - 2017 = 0 := eq_eq0'
    rw [eq9] at eq9'
    norm_num at eq9'
    linarith
  · -- Case where 4 + a = 0, so a = -4
    have ha : a = -4 := by linarith
    nlinarith [sq_nonneg (x 0 ^ 2 - x 1 ^ 2), sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 ^ 2 - 2), sq_nonneg (x 1 ^ 2 - 2)]