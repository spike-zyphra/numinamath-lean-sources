import Mathlib

/- For what base-6 digit $d$ is $2dd5_6$ divisible by the base 10 number 11? (Here $2dd5_6$ represents a base-6 number whose first digit is 2, whose last digit is 5, and whose middle two digits are both equal to $d$). -/
theorem number_theory_14496 : {d < 6 | 11 ∣ Nat.ofDigits 6 [5, d, d, 2]} = {4} := by 
  ext n
  simp
  norm_num [Nat.ofDigits]
  omega