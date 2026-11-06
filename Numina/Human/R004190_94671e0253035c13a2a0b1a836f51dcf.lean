import Mathlib

open Real

/- Prove that $\sin ^{3} 18^{\circ}+\sin ^{2} 18^{\circ}=1 / 8$. -/
theorem algebra_241536 : sin (π / 10) ^ 3 + sin (π / 10) ^ 2 = 1 / 8 := by
  calc _ = sin (π / 10) ^ 2 * (sin (3 * π / 10 - π / 5) + sin (3 * π / 10 + π / 5)) := by ring_nf; simp; nth_rw 3 [<-div_eq_mul_inv]; simp
       -- use sin (a + b) + sin (a - b) = 2 sin a cos b
       _ = sin (π / 10) ^ 2 * 2 * sin (3 * π / 10) * cos (π / 5) := by rw [sin_sub, sin_add]; ring
       _ = sin (π / 10) ^ 2 * 2 * sin (π / 2 - π / 5) * cos (π / 5) := by ring_nf
       _ = 2 * sin (π / 10) ^ 2 * cos (π / 5) ^ 2 := by rw [sin_pi_div_two_sub]; ring_nf
       -- multiply by $cos (π / 10) ^ 2$ and divide by $cos (π / 10) ^ 2$
       _ = 2 * sin (π / 10) ^ 2 * cos (π / 5) ^ 2 * cos (π / 10) ^ 2 / cos (π / 10) ^ 2 := by
          rw [mul_div_cancel_right₀]
          apply ne_of_gt
          apply sq_pos_of_pos
          apply cos_pos_of_mem_Ioo
          simp
          constructor
          linarith [pi_pos]
          linarith [pi_pos]
      -- use `sin_two_mul` twice
       _ = (2 * sin (π / 10) * cos (π / 10)) ^ 2 * cos (π / 5) ^ 2 / (2 * cos (π / 10) ^ 2) := by ring
       _ = sin (π / 5) ^ 2 * cos (π / 5) ^ 2 / (2 * cos (π / 10) ^ 2) := by rw [<-sin_two_mul]; ring_nf
       _ = (2 * sin (π / 5) * cos (π / 5)) ^ 2 / cos (π / 10) ^ 2 / 8 := by ring_nf
       _ = (sin (π / 2 - π / 10) / cos (π / 10)) ^ 2 / 8 := by rw [<-sin_two_mul]; ring_nf
       _ = 1 / 8 := by
        rw [sin_pi_div_two_sub, div_self]
        ring_nf
        apply ne_of_gt
        apply cos_pos_of_mem_Ioo
        simp
        constructor
        linarith [pi_pos]
        linarith [pi_pos]
