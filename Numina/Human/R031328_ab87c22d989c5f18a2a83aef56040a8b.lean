import Mathlib

open Real

/-Determine the smallest positive period of the function $y=\cos ^{2}x$.-/
theorem algebra_9315 {f : ℝ → ℝ} (hf : f = λ x => (cos x) ^ 2) :
IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
--Rewrite and simplify assumptions, then split goals
  rw [IsLeast, lowerBounds]; simp [hf]; constructor
  · apply pi_pos
-- Introduce assumptions on a new variable denoting any period of $f$
  intro a ha0 ha1
-- Prove that $a$ has to be greater or equal to $pi$
-- Plug in $x=pi/2$ to the assumptions to get an equation on $a$
  let h := ha1; apply_fun Function.eval (Real.pi/2) at h
  simp at h; symm at h; rw [sq_eq_zero_iff] at h
-- Apply cos_eq_zero_iff and solve for $a$
  rw [cos_eq_zero_iff] at h; rcases h with ⟨k, hk⟩; symm at hk
  rw [← sub_eq_iff_eq_add'] at hk
  rw [show (2 * (k:ℝ) + 1) * π / 2 - π / 2 = (k:ℝ) * π  by ring] at hk
-- Rewrite ha0 using hk, then find a lower bound on k
  rw [← hk, mul_pos_iff_of_pos_right] at ha0
  norm_cast at ha0; simp [Int.lt_iff_add_one_le] at ha0
-- Rewrite the final goal and prove it
  rw [← hk]; nth_rw 1 [← one_mul π]; rw [mul_le_mul_right]
  norm_cast; apply pi_pos; apply pi_pos