import Mathlib
/-If $10^{51} - 9$ is written as an integer in standard form, what is the sum of the integer's digits?-/
theorem number_theory_18639 : (Nat.digits 10 (10^51 - 9)).sum = 451 := by
  --Since $10^{51}$ is the least integer with $52$ digits, $10^{51}-9$ has 51 digits.  The ones digit is 1 and all the other digits are 9.  The sum of the digits is $9\cdot 50 + 1=\boxed{451}$.
  have h  : Nat.digits 10 (10^51 - 9)   =  (1::  (List.replicate (50) (9) )) := by
    norm_num
    simp
  rw [h]
  have h2 :  (1::  (List.replicate (50) (9) )).sum = 1 + 50 * 9 := by
    rw [List.sum_cons]
    rw [List.sum_replicate]
    ring_nf
  rw [h2]
