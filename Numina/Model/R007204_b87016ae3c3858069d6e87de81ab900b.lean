import Mathlib

theorem number_theory_66417 : 0 < 19^93 - 13^99 ∧ 162 ∣ 19^93 - 13^99 := by
  constructor
  · -- Show $19^{93} - 13^{99}$ is positive
    norm_num
  · -- Show $162$ divides $19^{93} - 13^{99}$
    norm_num