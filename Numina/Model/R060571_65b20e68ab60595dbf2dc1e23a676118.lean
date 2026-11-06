import Mathlib

open Finset Real

theorem algebra_177478 {x : ℕ → ℝ}
    (hx1 : x 1 = 1)
    (hxn : ∀ n ≥ 1, x (n + 1) = 1 + (x n)^2 / n) :
    x 2019 = 2019 := by 
  have hx : ∀ n : ℕ, x (n + 1) = (n + 1 : ℝ) := by
    intro n 
    induction n with 
    | zero =>
      norm_num 
      all_goals 
        simp [hx1]
    | succ n ih =>
      have h := hxn (n + 1) (by linarith)
      simp [show n + 1 ≥ 1 by omega] at h ⊢
      rw [ih] at h 
      simp [h]
      <;> field_simp <;> ring_nf <;> linarith
  have h_eq := hx 2018
  norm_num at h_eq ⊢ 
  <;> linarith