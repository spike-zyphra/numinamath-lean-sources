import Mathlib
open Real
theorem inequalities_112544 {f : ℝ → ℝ}
  (h₀ : ∀ x y, 0 < x → 0 < y → log (x * y) ≤ f x + f y - x - y)
  (h₁ : ∀ x y, 0 < x → 0 < y → f x + f y - x - y ≤ f (x * y) - x * y) :
  ∀ x, 0 < x → f x = log x + x := by
  intro x hx
  have h1 : f 1 = 1 := by
    have h2 := h₀ 1 1 (by norm_num) (by norm_num)
    have h3 := h₁ 1 1 (by norm_num) (by norm_num)
    norm_num [log_one] at h2 h3
    linarith
  have h4 : log x + x ≤ f x := by
    specialize h₀ x 1 hx (by norm_num)
    simp [show f 1 = 1 by linarith [h1]] at h₀
    linarith
  have h5 : f x ≤ log x + x := by
    have h14 := h₁ x (1 / x) hx (by positivity)
    have h15 := h₀ x (1 / x) hx (by positivity)
    have h14' : f x + f (1 / x) - x - (1 / x) ≤ 0 := by
      have h16 : f (x * (1 / x)) - x * (1 / x) = 0 := by
        have h17 : f (x * (1 / x)) = 1 := by
          have h18 : x * (1 / x) = 1 := by
            field_simp
          rw [h18]
          linarith [h1]
        have h19 : x * (1 / x) = 1 := by
          field_simp
        rw [h19] at *
        nlinarith [h17]
      have h18 : f x + f (1 / x) - x - (1 / x) ≤ f (x * (1 / x)) - x * (1 / x) := by
        apply h₁ x (1 / x) hx (by positivity)
      linarith
    have h15' : 0 ≤ f x + f (1 / x) - x - (1 / x) := by
      have h18 : log (x * (1 / x)) ≤ f x + f (1 / x) - x - (1 / x) := by
        apply h₀ x (1 / x) hx (by positivity)
      have h19 : log (x * (1 / x)) = 0 := by
        have h20 : x * (1 / x) = 1 := by
          field_simp
        rw [h20]
        simp [log_one]
      linarith
    have h16 : f x + f (1 / x) = x + (1 / x) := by linarith
    have h7 := h₀ (1 / x) 1 (by positivity) (by norm_num)
    have h8 : log ( (1 / x) * (1 : ℝ) ) ≤ f (1 / x) + f 1 - (1 / x) - (1 : ℝ) := by
      simpa using h7
    have h9 : log ( (1 / x) * (1 : ℝ) ) = log (1 / x) := by
      simp
    rw [h9] at h8
    have h10 : log (1 / x) = - log x := by
      simp [log_div, log_one]
    rw [h10] at h8
    simp [show f 1 = 1 by linarith [h1]] at h8
    nlinarith [h16, h8]
  linarith