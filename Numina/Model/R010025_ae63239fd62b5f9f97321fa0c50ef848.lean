import Mathlib

theorem algebra_18845 (a : ℕ → ℝ) (h : ∃ q, ∀ n, a (n + 1) = a n * q) (h₀ : a 0 = 125 / 9) (h₁ : a 1 = 25 / 3) (h₂ : a 2 = 5) (h₃ : a 3 = 3) :
    a 7 = 243 / 625 := by
  rcases h with ⟨q, hq⟩

  have hq1 : a 1 = a 0 * q := hq 0
  rw [h₀] at hq1
  rw [h₁] at hq1
  have hq2 : q = 3 / 5 := by
    linarith

  have ha4 : a 4 = a 3 * q := hq 3
  rw [h₃, hq2] at ha4

  have ha5 : a 5 = a 4 * q := hq 4
  rw [ha4, hq2] at ha5

  have ha6 : a 6 = a 5 * q := hq 5
  rw [ha5, hq2] at ha6

  have ha7 : a 7 = a 6 * q := hq 6
  rw [ha6, hq2] at ha7

  norm_num at ha7 ⊢
  linarith