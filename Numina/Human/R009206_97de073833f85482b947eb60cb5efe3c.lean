import Mathlib

/-Find the smallest positive period of the function $y = 3 \tan\left(2x + \frac{5\pi}{6}\right)$.-/
theorem algebra_9256 {f : ℝ → ℝ} (hf : f = fun x => 3 * Real.tan (2 * x + 5 * Real.pi / 6)) :
IsLeast {T | 0 < T ∧ f = fun x => f (x + T)} (Real.pi / 2) := by
--Rewrite assumptions and split goals
  rw [IsLeast, lowerBounds]; simp
  constructor; constructor; exact Real.pi_pos
-- Prove that $pi/2$ is a period of $f$
  · ext x; simp [hf]
    rw [mul_add, mul_div, mul_div_cancel_left₀]
    nth_rw 2 [add_comm]; rw [← add_assoc]; nth_rw 3 [add_comm]
    rw [Real.tan_add_pi]; norm_num
-- Prove that if $a$ is any positive period, $a$ has to be greater or equal to $pi/2$
  intro a ha1 ha2; simp [hf] at ha2
  let h' := ha2
-- Plug in $x=-pi/6$ to h', we get an equation on $a$
  apply_fun (Function.eval (-Real.pi/6)) at h'
  simp at h'; rw [show 2*(-Real.pi/6)+5*Real.pi/6=Real.pi/2 by ring] at h'
-- Solve for $a$ by applying Real.tan_eq_zero_iff
  simp at h'; symm at h'; rw [Real.tan_eq_zero_iff] at h'
  rcases h' with ⟨k, hk⟩; ring_nf at hk; rw [← sub_eq_iff_eq_add'] at hk
  rw [show (k:ℝ)*Real.pi*(1/2)-Real.pi*(1/2)=((k:ℝ)-1)*Real.pi*(1/2) by ring] at hk
-- Find a lowerbound of $k$ from the positivity of $a$
  have : 0 < a * 2 := by linarith
  rw [← hk] at this; simp at this
  rw [mul_pos_iff_of_pos_right, sub_pos] at this; norm_cast at this
  rw [Int.lt_iff_add_one_le] at this; simp at this
-- Rewrite the final goal and prove it by contradiction
  rw [div_le_iff₀, ← hk, mul_comm, ← mul_assoc]; nth_rw 1 [← one_mul Real.pi]
  rw [mul_le_mul_iff_of_pos_right, one_div_mul_eq_div]
  rw [le_div_iff₀, one_mul]; norm_cast
  rw [le_sub_iff_add_le]; simp
  by_contra h'; push_neg at h'
  replace h' : k = 2 := by linarith
  simp [h'] at hk; ring_nf at hk
-- Plug in $x=-pi/4$ to ha2 and compute the values of trig functions
  let h := ha2; apply_fun (Function.eval (-Real.pi/4)) at h
  ring_nf at h; rw [← hk] at h; ring_nf at h
  apply mul_right_cancel₀ at h
  rw [mul_one_div, show Real.pi*(5/6)=Real.pi-Real.pi/6 by ring] at h
  rw [Real.tan_pi_sub, Real.tan_pi_div_six, Real.tan_pi_div_three] at h
-- Derive a contradiction from these values
  rw [← neg_div] at h; symm at h
  rw [div_eq_iff, ← Real.sqrt_mul, Real.sqrt_mul_self] at h
  linarith; norm_num; norm_num; norm_num; norm_num; norm_num
  apply Real.pi_pos; norm_num; apply Real.pi_pos