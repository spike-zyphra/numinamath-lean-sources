import Mathlib

theorem algebra_131054 {x : ℤ} {f : ℤ → ℤ}
    (hf : ∀x, f x = 2 * x - 1)
    (h : f^[2000] x = 2^2001 + 1) :
    x = 3 := by
  have h₁ : ∀ n : ℕ, ∀ x : ℤ, (f^[n] x : ℤ) = 2 ^ n * x - (2 ^ n - 1) := by
    intro n x
    induction n with
    | zero =>
      simp [hf, Function.iterate_zero]
    | succ n ih =>
      simp [hf, Function.iterate_succ_apply', ih]
      ring_nf at *
  nlinarith [h₁ 2000 x]
