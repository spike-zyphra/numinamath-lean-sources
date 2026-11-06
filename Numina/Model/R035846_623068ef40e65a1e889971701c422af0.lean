import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_295097
  (x y z : ℝ)
  (hx : x ∈ Icc 0 1)
  (hy : y ∈ Icc 0 1)
  (hz : z ∈ Icc 0 1)
  (h : (1 - x) * (1 - y) * (1 - z) = x * y * z) :
  (1 / 4 ≤ (1 - x) * y ∨ 1 / 4 ≤ (1 - y) * z ∨ 1 / 4 ≤ (1 - z) * x) ∧
  (1 / 4 ≥ (1 - x) * y ∨ 1 / 4 ≥ (1 - y) * z ∨ 1 / 4 ≥ (1 - z) * x) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rcases hz with ⟨hz0, hz1⟩
  constructor
  · -- Show that at least one of the three real numbers $(1-x) y, (1-y) z, (1-z) x$ is greater than or equal to $\frac{1}{4}$.
    by_contra h1
    push_neg at h1
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2), 
              mul_nonneg (show 0 ≤ (1 - x) by linarith) (show 0 ≤ y by linarith), 
              mul_nonneg (show 0 ≤ (1 - y) by linarith) (show 0 ≤ z by linarith), 
              mul_nonneg (show 0 ≤ (1 - z) by linarith) (show 0 ≤ x by linarith)]
  · -- Show that at least one of the three real numbers $(1-x) y, (1-y) z, (1-z) x$ is less than or equal to $\frac{1}{4}$.
    by_contra h2
    push_neg at h2
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1 / 2),
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith),
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ z by linarith),
      mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith),
      mul_nonneg (show 0 ≤ (1 - x) by linarith) (show 0 ≤ (1 - y) by linarith), 
      mul_nonneg (show 0 ≤ (1 - y) by linarith) (show 0 ≤ (1 - z) by linarith), 
      mul_nonneg (show 0 ≤ (1 - z) by linarith) (show 0 ≤ x by linarith)
      ]