import Mathlib

theorem number_theory_157417 (n : ℤ) (hn : n = 2013^2014) :
    ∀ k : ℤ, k ≠ 2013 → (2013 - k) ∣ (n - k^2014) := by
  intro k hk
  rw [hn]
  apply sub_dvd_pow_sub_pow