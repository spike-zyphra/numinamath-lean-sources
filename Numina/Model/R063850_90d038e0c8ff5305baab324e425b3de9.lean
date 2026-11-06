import Mathlib

theorem algebra_209979 (x : ℕ → ℤ)
    (hx1 : x 1 = 1)
    (hxn : ∀ n ≥ 1, x (n + 1) = x n + 2 * n + 1) :
    x 2023 = 2023 ^ 2 := by 
  have h : ∀ n, x (n + 1) = (n + 1 : ℕ) ^ 2 := by 
    intro n 
    induction n with 
    | zero =>
      simp [hx1]
    | succ n ih =>
      simp [hxn (n + 1) (by linarith), ih]
      <;> ring_nf <;> omega
  have h2022 := h 2022
  norm_num at h2022 ⊢ 
  linarith