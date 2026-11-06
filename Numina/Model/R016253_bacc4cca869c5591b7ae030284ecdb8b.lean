import Mathlib

open Finset

theorem algebra_12896 {f : ℝ → ℝ} (hf : ∀ x, f x = x / (x - 1)) :
    f^[2020] 802 = 802 := by 
  have h1 : ∀ x, f x = x / (x - 1) := hf
  have h2 : f^[2] 802 = 802 := by
    simp [Function.iterate_succ_apply', h1]
    <;> norm_num
  have h3 : ∀ n, f^[2 * n] 802 = 802 := by 
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have h4 : f^[2 * (n + 1 : ℕ)] 802 = f^[2 * n + 2] 802 := by 
        ring_nf
      rw [h4]
      have h5 : f^[2 * n + 2] 802 = f^[2 * n] (f^[2] 802) := by 
        rw [Function.iterate_add_apply]
      rw [h5]
      rw [h2]
      all_goals try exact ih
      all_goals try linarith
  have h4 : 2020 = 2 * (1010 : ℕ) := by 
    norm_num
  rw [h4]
  apply h3 1010
  all_goals try linarith
  all_goals try try { norm_num }