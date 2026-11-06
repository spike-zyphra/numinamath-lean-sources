import Mathlib

open Finset List

theorem algebra_11449 (a b c d : ℤ) (h : [a, b, c, d] ~ [1, 2, 3, 4] ):
    (a * b + b * c + c * d + d * a ≤   25) ∧ 
    ([a, b, c, d] = [1, 2, 4, 3] → (a * b + b * c + c * d + d * a = 25)) := by 
  constructor
  · -- First part: Prove that the sum of products is at least 25 regardless of permutation.
    have eq_aux : a * b + b * c + c * d + d * a = (a + c) * (b + d) := by ring
    rw [eq_aux]
    have sum_eq : a + b + c + d = 10 := by 
      obtain heq := List.Perm.sum_eq h
      simp at heq
      rw [← heq]
      ring
    let x := a + c
    calc 
      _ = x * (10 - x) := by 
        unfold x
        rw [← sum_eq]
        ring
      _ ≤  25 := by 
        nlinarith [sq_nonneg (x - 5)]
  · intro h1
    -- Second part: Prove that if it's in a specific order, then the value must be exactly 25.
    simp at h1
    obtain ⟨ha, hb, hc, hd⟩ := h1
    rw [ha, hb, hc, hd]
    norm_num