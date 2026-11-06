import Mathlib

open Real

theorem number_theory_314599 (p : ℕ → ℕ) (hp : ∀ n, Nat.Prime (p n))
    (hp' : ∀ n, p n > p (n - 1)) (x : ℕ → ℝ) (hx : 0 < x 0 ∧ x 0 < 1)
    (h : ∀ k, x (k + 1) = if x k = 0 then 0 else (p (k + 1)) / x k % 1) :
    (∃ n, x n = 0) ↔ x 0 = 1 / 2 := by

  have h4 : p 0 > p 0 := by 
    specialize hp' 0
    norm_num at hp' ⊢
    <;> omega

  linarith