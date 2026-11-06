import Mathlib

open Real

theorem number_theory_97287 (p : ℕ → ℕ) (hp : ∀ n, Nat.Prime (p n))
    (hp1 : ∀ n, p n > p (n - 1)) (x : ℕ → ℝ) (hx : 0 < x 0 ∧ x 0 < 1)
    (hxp : ∀ k, x (k + 1) = if x k = 0 then 0 else (p (k + 1)) / x k % 1) :
    (∃ n, x n = 0) ↔ x 0 = 1 / 2 := by

  have h1 := hp1 0

  have h3 : p 0 > p 0 := by 
    have h4 : p 0 > p (0 - 1) := h1
    have h5 : p (0 - 1) = p 0 := by 
      simp
    rw [h5] at h4
    linarith

  linarith