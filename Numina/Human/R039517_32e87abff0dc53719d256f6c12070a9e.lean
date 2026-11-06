import Mathlib

open Real Set
open scoped Real

/- Find the maximum and minimum values of the function $y=3-4\sin x-\cos^2x$.-/
theorem algebra_9408 (f : ℝ → ℝ) (hf : f = λ x => 3 - 4 * sin x - cos x ^ 2) :
    IsGreatest (range f) 7 ∧ IsLeast (range f) (-1) := by
  -- The key fact here is that $3 - 4 * sin x - cos x ^ 2 = (sin x - 2) ^ 2 - 2$.
  have key (x : ℝ) : 3 - 4 * sin x - cos x ^ 2 = (sin x - 2) ^ 2 - 2 := by
    rw [cos_sq']
    ring
  constructor
  . constructor
    -- Verify that 7 is in the range of $f(x)$.
    . simp [hf]
      use -(π / 2)
      rw [sin_neg, sin_pi_div_two, cos_neg, cos_pi_div_two]
      norm_num
    -- Prove that 7 is the greatest in the range of $f(x)$.
    intro y hy
    rw [hf, mem_range] at hy
    rcases hy with ⟨x, hx⟩
    rw [← hx, key]
    have := sin_mem_Icc x
    simp at this
    nlinarith
  constructor
  -- Verify that -1 is in the range of $f(x)$.
  . simp [hf]
    use π / 2
    rw [sin_pi_div_two, cos_pi_div_two]
    norm_num
  -- Prove that -1 is the least in the range of $f(x)$.
  intro y hy
  rw [hf, mem_range] at hy
  rcases hy with ⟨x, hx⟩
  rw [← hx, key]
  have := sin_mem_Icc x
  simp at this
  nlinarith
