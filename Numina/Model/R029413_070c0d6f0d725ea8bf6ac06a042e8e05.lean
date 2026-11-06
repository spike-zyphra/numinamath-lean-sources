import Mathlib

open Finset Nat

theorem number_theory_94854 {f : ℕ → ℝ}
(hf : ∀ n, f n = (∑ d ∈ (n.divisors), d) / n) :
f 768 - f 384 = 1 / 192 := by
  rw [hf 768, hf 384]
  have h1 : (∑ d in (768 : ℕ).divisors, d) = 2044 := by
    native_decide
  have h2 : (∑ d in (384 : ℕ).divisors, d) = 1020 := by
    native_decide
  rw [h1, h2]
  norm_num