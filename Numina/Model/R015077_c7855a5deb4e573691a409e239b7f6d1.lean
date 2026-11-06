import Mathlib

open Finset Real

theorem algebra_324538 {f : ℕ → ℕ → ℕ}
    (hf1 : f 1 1 = 1)
    (hfm : ∀ m n, f (m + 1) n = f m n + 2 * (m + n))
    (hfn : ∀ m n, f m (n + 1) = f m n + 2 * (m + n - 1)) :
    (∀ m n, f m n = 2 * m * n - 1) ∧
    (∀ n, ∑ i ∈ range n, (Real.sqrt (f (i + 1) (i + 1))) / 2 ^ i < 6) := by

  exfalso
  have eq1 := hfm 0 1
  simp at eq1
  rw [hf1] at eq1
  omega