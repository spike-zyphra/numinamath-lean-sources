import Mathlib

open Finset

theorem number_theory_210211 {a : ℕ} (ha : a > 0) :
    ∀ i ∈ Icc 2 a, ∀ j ∈ Icc 1 (i - 1), (i * (i - 1) + j ^ 2 + 1) ≠
      (i * (i - 1) + j ^ 2 + 2) ∧
      (i * (i - 1) + j ^ 2 + 2) ≠ (i * (i - 1) + j ^ 2 + 3) ∧
      (i * (i - 1) + j ^ 2 + 3) ≠ (i * (i - 1) + j ^ 2 + 4) := by 
  intro i hi j hj 
  constructor
  · -- Show that $k \neq k + 1$
    omega 
  constructor 
  · -- Show that $k + 1 \neq k + 2$
    omega 
  · -- Show that $k + 2 \neq k + 3$
    omega