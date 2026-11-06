import Mathlib

open Finset Real

theorem algebra_212505 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 6)
    (han : ∀ n > 1, a n = a (n - 1) - 1 / n + 2 / (n + 1) - 1 / (n + 2)) :
    a 100 = 1 / 10302 := by 
  have h100 : ∀ (n : ℕ), a (n + 1) = 1 / ((↑n + 1 + 1 : ℝ) * (↑n + 1 + 2 : ℝ)) := by
    intro n 
    induction n with 
    | zero =>
      rw [ha1]
      norm_num 
    | succ n ih =>
      have h2 := han ((n + 1 + 1 : ℕ)) (by linarith)
      simp [show n + 1 + 1 = n + 2 by omega] at h2 ⊢
      rw [h2]
      rw [ih]
      field_simp 
      ring 
  specialize h100 99 
  norm_num at h100 ⊢ 
  linarith