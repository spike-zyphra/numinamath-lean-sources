import Mathlib

theorem number_theory_271300 {M X Y : ℕ} (h₀ : M ≠ X) (h₁ : M ≠ Y) (h₂ : X ≠ Y)
    (h₃ : ∀ n ≥ 1, (10 ^ n - 1) * M + X * 10 ^ n + Y = (10 ^ n - 1) * X + M * 10 ^ n + Y) :
    M = 0 ∧ X = 4 ∧ Y = 5 := by
  have h4 := h₃ 1 (by norm_num)
  norm_num at h4
  have h5 : X = M := by 
    omega
  exfalso
  exact h₀ (by omega)