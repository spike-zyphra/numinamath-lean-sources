import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_322776 (a : ℝ) (ha : |a| ≤ 1) (f : ℝ → ℝ)
  (hf : f = λ x => a * x ^ 2 + x - a) :
  ∀ x ∈ Icc (-1) 1, |f x| ≤ 5 / 4 := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h1 : -1 ≤ x := hx1
  have h2 : x ≤ 1 := hx2
  have h3 : -1 ≤ a := by linarith [abs_le.mp ha]
  have h4 : a ≤ 1 := by linarith [abs_le.mp ha]
  have h5 : f x = a * x ^ 2 + x - a := by simp [hf]
  have h6 : -5 / 4 ≤ a * x ^ 2 + x - a := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (a + 1 / 2),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 by linarith)
      ]
  have h7 : a * x ^ 2 + x - a ≤ 5 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (a + 1 / 2),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x + 1 by linarith) (show (0 : ℝ) ≤ 1 by linarith)
      ]
  rw [h5]
  apply abs_le.mpr
  constructor <;> nlinarith