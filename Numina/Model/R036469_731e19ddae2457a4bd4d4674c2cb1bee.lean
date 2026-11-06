import Mathlib

open Finset

theorem algebra_139780 {f : ℕ → ℤ}
    (hf : ∀ n, f n = ∑ i ∈ Icc 1 n, Nat.factorial i) :
    ∃ a b : Polynomial ℤ, ∀ n, f (n + 2) = a.eval (n : ℤ) * f (n + 1) -
      b.eval (n : ℤ) * f n := by 
  use (Polynomial.X + Polynomial.C (3 : ℤ))
  use (Polynomial.X + Polynomial.C (2 : ℤ))
  intro n 
  rw [hf (n + 2), hf (n + 1), hf n]
  simp [sum_Icc_succ_top, Nat.factorial]
  <;> ring_nf <;> omega