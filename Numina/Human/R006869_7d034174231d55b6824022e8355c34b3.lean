import Mathlib

/-
Let $p$ be an arbitrary prime number. Prove that its square root, $\sqrt{p}$, is an irrational number.
-/

theorem number_theory_641948 (p : ℕ) (hp : Nat.Prime p):
  Irrational (Real.sqrt ((p : ℝ))) := by
  
  exact Nat.Prime.irrational_sqrt hp
