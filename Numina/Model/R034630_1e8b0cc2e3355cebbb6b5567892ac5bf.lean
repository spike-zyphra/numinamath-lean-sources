import Mathlib

theorem number_theory_314384 (a : ℕ → ℤ)
    (h₀ : a 1 = 8)
    (h₁ : a 2 = 20)
    (h₂ : ∀ n, a (n + 2) = a (n + 1)^2 + 12 * a (n + 1) * a n + a (n + 1) + 11 * a n) :
    ∀ n, ¬∃ x y z, a n = x^7 + y^7 + z^7 := by

  have h3 : a 2 = a 1^2 + 12 * a 1 * a 0 + a 1 + 11 * a 0 := by
    specialize h₂ 0
    simpa using h₂
  rw [h₀] at h3
  rw [h₁] at h3
  have h4 : (107 : ℤ) * (a 0) = -52 := by
    nlinarith

  have h7 : (107 : ℤ) ∣ (-52 : ℤ) := by
    use (a 0)
    linarith

  have h8 : (107 : ℤ) ∣ (-52 : ℤ) := h7

  norm_num at h8
  all_goals omega