import Mathlib

/- Let's prove that $2^{888}-888$ is divisible by 61. -/
theorem number_theory_179850 : 61 ∣ (2^888 - 888) := by ring_nf; norm_num