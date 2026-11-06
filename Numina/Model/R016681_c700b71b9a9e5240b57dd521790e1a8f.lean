import Mathlib

theorem number_theory_129203 (f : ℕ → ℕ) (h₀ : f 0 = 0)
    (h₁ : ∀ n, (f (2 * n + 1)) ^ 2 - (f (2 * n)) ^ 2 = 6 * f n + 1) (h₂ : ∀ n, f (2 * n) > f n) :
    Set.ncard {x | ∃ n, x = f n ∧ x < 2004} = 128 := by
  have h3 : f 0 < f 0 := by
    specialize h₂ 0
    have h4 : f (2 * 0) > f 0 := h₂
    have h5 : 2 * 0 = 0 := by norm_num
    rw [h5] at h4
    omega
  have h6 : f 0 < f 0 := h3
  have h7 : f 0 < f 0 := h6
  linarith [h₀, h7]