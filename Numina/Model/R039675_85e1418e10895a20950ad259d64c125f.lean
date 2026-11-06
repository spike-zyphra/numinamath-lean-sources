import Mathlib

theorem algebra_57878 {a b c k : ℝ} (h₀ : a + b + c = k) (h₁ : ∃ d, b = a + d ∧ c = b + d)
    (h₂ : ∃ r, b = a * r ∧ c = b * r + k / 6) :
    a = 2 * k / 3 ∧ b = k / 3 ∧ c = 0 := by
  rcases h₁ with ⟨d, h₃, h₄⟩
  rcases h₂ with ⟨r, h₅, h₆⟩
  have h₇ : a + b + c = k := h₀
  have eq1 : c = a + 2 * d := by 
    linarith [h₃, h₄]
  have eq2 : a + d = k / 3 := by
    nlinarith [h₀, eq1]
  have eq3 : b = k / 3 := by 
    nlinarith [h₃, eq2]
  have eq4 : c = 2 * k / 3 - a := by 
    nlinarith [eq1, eq2]
  have eq5 : k / 3 = a * r := by 
    have eq3' : b = k / 3 := eq3 
    rw [eq3'] at h₅ 
    linarith 
  have eq6 : 2 * k / 3 - a = (k / 3) * r + k / 6 := by 
    have eq4' : c = 2 * k / 3 - a := eq4 
    have eq3' : b = k / 3 := eq3 
    rw [eq4', eq3'] at h₆ 
    linarith 
  have eq7 : a * (-2 * r ^ 2 + 3 * r - 2) = 0 := by
    have eq8 : 3 * k - 6 * a - 2 * k * r = 0 := by
      linarith [eq6]
    have eq9 : k = 3 * a * r := by 
      have h10 : k / 3 = a * r := eq5 
      have h11 : k = 3 * (k / 3) := by linarith 
      rw [h10] at h11 
      linarith 
    rw [eq9] at eq8 
    linarith 
  cases' (mul_eq_zero.mp eq7) with h1 h2 
  · -- Case `a = 0`.
    have ha0 : a = 0 := h1 
    have hk0 : k = 0 := by 
      have h5' : k / 3 = a * r := eq5 
      rw [ha0] at h5' 
      have h50 : k / 3 = 0 := by 
        linarith 
      linarith 
    have hb0 : b = 0 := by
      linarith [eq3, hk0] 
    have hc0 : c = 0 := by 
      linarith [eq4, ha0, hk0] 
    constructor 
    · -- Show a = 2 * k / 3 
      rw [ha0, hk0] 
      linarith 
    constructor 
    · -- Show b = k / 3 
      rw [hb0, hk0] 
      linarith 
    · -- Show c = 0 
      linarith [hc0] 
  · -- Case `-2 * r ^ 2 + 3 * r - 2 = 0`. 
    have h21 : -2 * r ^ 2 + 3 * r - 2 = 0 := by linarith 
    have h21' : -2 * r ^ 2 + 3 * r - 2 = 0 := h21 
    nlinarith [sq_nonneg (r - 3 / 4), sq_nonneg (r - 2), sq_nonneg (r - 1)]