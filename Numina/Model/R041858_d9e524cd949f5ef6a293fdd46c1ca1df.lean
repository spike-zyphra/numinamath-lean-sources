import Mathlib

open Real
theorem number_theory_163425 {f : ℝ → ℝ} (hf : ∀ x, f x = x + ⌊Real.sqrt x⌋)
    (m : ℕ) :
    ∃ n, ∃ k, n^2 = f^[k] m := by
  use Real.sqrt (f^[0] m)
  use 0
  simp [hf]
  all_goals
    ring_nf <;> norm_num