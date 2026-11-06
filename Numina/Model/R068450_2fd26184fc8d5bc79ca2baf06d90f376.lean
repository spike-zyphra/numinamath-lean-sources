import Mathlib

open Finset

theorem algebra_608348 {f : ℕ → ℕ → ℕ} (hf : ∀ n, f n 0 = n)
    (hfd : ∀ n d, f n (d + 1) = f n d + 1) :
    ∀ a d, f (2 ^ a) d = 2 ^ a + d := by
  intro a d
  induction d with
  | zero =>
    simp [hf]
  | succ d ih =>
    calc
      f (2 ^ a) (d + 1) = f (2 ^ a) d + 1 := hfd (2 ^ a) d
      _ = (2 ^ a + d) + 1 := by rw [ih]
      _ = 2 ^ a + (d + 1) := by ring