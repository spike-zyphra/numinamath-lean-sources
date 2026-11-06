import Mathlib
open Real Set

theorem calculus_9310 (f : ℝ → ℝ) (m : ℝ) (hf : f = fun x => x ^ 3 - m * x ^ 2 - x + 1)
    (h : ∀ x, deriv f x ≥ abs x - 7 / 4) :
    m ∈ Icc (-1) 1 := by
  have hf' : ∀ x, deriv f x = 3 * x ^ 2 - 2 * m * x - 1 := by
    intro x
    rw [hf]
    simp [deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm]
    all_goals field_simp
    <;> ring_nf <;> field_simp
  have h1 := h (1 / 2)
  have h1' : deriv f (1 / 2) ≥ abs (1 / 2 : ℝ) - 7 / 4 := h1
  have h2 := h (-1 / 2)
  have h2' : deriv f (-1 / 2) ≥ abs (-1 / 2 : ℝ) - 7 / 4 := h2
  have eq1 : deriv f (1 / 2) = 3 * (1 / 2 : ℝ) ^ 2 - 2 * m * (1 / 2) - 1 := hf' (1 / 2)
  have eq2 : deriv f (-1 / 2) = 3 * (-1 / 2 : ℝ) ^ 2 - 2 * m * (-1 / 2) - 1 := hf' (-1 / 2)
  rw [eq1] at h1'
  rw [eq2] at h2'
  norm_num [abs_of_pos, abs_of_neg] at h1' h2'
  constructor
  · -- Show m ≥ -1
    linarith
  · -- Show m ≤ 1
    linarith