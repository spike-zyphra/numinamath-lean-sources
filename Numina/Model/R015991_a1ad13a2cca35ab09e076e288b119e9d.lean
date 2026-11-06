import Mathlib

theorem algebra_141678 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 4 + 7 * x ^ 3 + 3 * x - 5)
    (k : ℝ) (h : ∀ x1 x2 x3 x4 : ℝ, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
      Collinear ℝ {(x1, f x1), (x2, f x2), (x3, f x3), (x4, f x4)}) :
    k = -7 / 8 := by
  have h1 := h 1 1 1 1 
  norm_num [hf, Set.mem_insert_iff, Set.mem_singleton_iff, collinear_pair] at h1