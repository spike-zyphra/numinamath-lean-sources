import Mathlib

theorem number_theory_7884 {n : ℤ} (hn : n = 38) :
    n % 10 = 8 ∧ ∃ k, n = k^2 + 2 ∧ ∃ p, n = 2 * p ∧ Prime p := by
  rw [hn]
  constructor
  · -- Show n % 10 = 8
    norm_num
  · -- Show that there exists a k such that n = k^2 + 2
    use 6
    constructor
    · -- Show that 38 = 6^2 + 2
      norm_num
    · -- Show that there exists a prime p such that 38 = 2 * p
      use 19
      all_goals norm_num
      <;> native_decide