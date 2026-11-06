import Mathlib
open Polynomial
theorem algebra_239179 : ∃ P1 P2 P3 : ℝ[X], P1 ≠ P2 ∧ P2 ≠ P3 ∧ P3 ≠ P1 ∧ (∀ x : ℝ, P1.eval (x ^ 2 + 1) = P1.eval x ^ 2 + 1) ∧ (∀ x : ℝ, P2.eval (x ^ 2 + 1) = P2.eval x ^ 2 + 1) ∧ (∀ x : ℝ, P3.eval (x ^ 2 + 1) = P3.eval x ^ 2 + 1):= by 
  use (X : ℝ[X])
  use ((X) ^ 2 + 1)
  use ((X) ^ 4 + 2 * (X) ^ 2 + 2)
  constructor
  · -- Show that $P_1 \neq P_2$
    intro h
    have h1 := congr_arg (fun p => p.eval 0) h
    norm_num at h1
  constructor
  · -- Show that $P_2 \neq P_3$
    intro h
    have h1 := congr_arg (fun p => p.eval 0) h
    norm_num at h1
  constructor
  · -- Show that $P_3 \neq P_1$
    intro h
    have h1 := congr_arg (fun p => p.eval 0) h
    norm_num at h1
  constructor
  · -- Show that $\forall x : \mathbb{R}, P_1(x^2+1) = P_1(x)^2 + 1$
    intro x
    simp [pow_two]
  constructor
  · -- Show that $\forall x : \mathbb{R}, P_2(x^2+1) = P_2(x)^2 + 1$
    intro x
    simp [pow_two]
    <;> ring
  · -- Show that $\forall x : \mathbb{R}, P_3(x^2+1) = P_3(x)^2 + 1$
    intro x
    simp [pow_two]
    <;> ring