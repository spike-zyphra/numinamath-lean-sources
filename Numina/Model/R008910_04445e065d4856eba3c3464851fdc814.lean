import Mathlib

theorem number_theory_2476 : (max (max (max (max (-1.1 : ℝ) (-1.01)) (-1.001)) (-1.0101)) (-1.00101)) / (min (min (min (min (-1.1 : ℝ) (-1.01)) (-1.001)) (-1.0101)) (-1.00101)) = 0.91 := by
  norm_num [max_assoc, max_comm, max_left_comm, min_assoc, min_comm, min_left_comm]