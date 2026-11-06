import Mathlib

open Finset

theorem algebra_93192 {f : ℝ → ℝ → ℝ} (hf : ∀ x y, f x y = (x + y) / 2)
    (x y z : ℝ) :
    x + (f y z) = f (x + y) (x + z) ∧
    f x (f y z) = f (f x y) (f x z) := by 
  constructor
  · -- Proof of x + (f y z) = f (x + y) (x + z)
    rw [hf y z, hf (x + y) (x + z)]
    ring_nf
  · -- Proof of f x (f y z) = f (f x y) (f x z)
    simp [hf]
    <;> ring_nf <;> simp [hf]
    <;> ring_nf