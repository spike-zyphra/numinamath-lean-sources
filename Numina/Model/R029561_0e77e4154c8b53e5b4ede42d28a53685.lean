import Mathlib

theorem number_theory_4810 (d n : ℕ) (_ : 0 < d) (h₁ : 0 < n) (h₂ : d ∣ n) :
    (2^d : ℤ) - 1 ∣ (2^n - 1) := by
  rcases h₂ with ⟨k, hk⟩
  have h3 : n = d * k := by linarith
  rw [show n = d * k by linarith]
  have h4 : ((2 : ℤ) ^ d - 1) ∣ ((2 : ℤ) ^ (d * k) - 1) := by
    have h5 : ((2 : ℤ) ^ (d * k) - 1) = ((2 : ℤ) ^ d) ^ k - 1 := by 
      ring_nf
    rw [h5]
    have h7 : ((2 : ℤ) ^ d - 1) ∣ (((2 : ℤ) ^ d) ^ k - 1) := by
      apply sub_one_dvd_pow_sub_one
    exact h7
  exact h4