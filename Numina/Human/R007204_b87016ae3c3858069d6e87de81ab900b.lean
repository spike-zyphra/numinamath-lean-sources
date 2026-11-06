import Mathlib

/- Show that $19^{93} - 13^{99}$ is a positive integer divisible by $162$. -/
theorem number_theory_66417 : 0 < 19^93 - 13^99 ∧ 162 ∣ 19^93 - 13^99 := by 
  norm_num