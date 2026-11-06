import Mathlib

theorem algebra_215064 (P : Polynomial ℤ) :
    (P.eval 6 ≠ 5 ∨ P.eval 14 ≠ 9) := by
  by_contra h
  push_neg at h
  have h1 : (14 - (6 : ℤ)) ∣ (P.eval 14 - P.eval 6) := by
    apply Polynomial.sub_dvd_eval_sub
  have h2 : P.eval 14 - P.eval 6 = 4 := by
    rw [h.1, h.2]
    norm_num
  rw [show (14 - (6 : ℤ) ) = 8 by norm_num] at h1
  rw [h2] at h1
  norm_num at h1