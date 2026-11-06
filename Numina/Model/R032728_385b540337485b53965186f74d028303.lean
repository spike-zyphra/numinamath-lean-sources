import Mathlib
open Nat

theorem number_theory_1857 (p : ℕ → ℕ) (hp₀ : p 1 = 2) (hp : ∀ n, p (n + 1) > p n)
    (hp' : ∀ n, Nat.Prime (p n)) :
    ¬ Summable fun i => (1 / p i : ℝ) := by
  have h1 := hp 0
  -- Then, p 1 > p 0.
  -- Since p 1 = 2 from hp₀, we can conclude p 0 < 2.
  have h3 : p 0 < 2 := by
    have h4 : p 1 = 2 := hp₀
    have h5 : p 1 > p 0 := hp 0
    linarith [h4]
  -- But for a prime number, we must have p 0 ≥ 2
  have h5 : p 0 > 1 := by 
    have h6 : Nat.Prime (p 0) := hp' 0
    exact Nat.Prime.two_le h6
  omega