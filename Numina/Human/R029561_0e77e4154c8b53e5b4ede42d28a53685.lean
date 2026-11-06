import Mathlib

/- If \( d \) and \( n \) are positive integers such that \( d \) divides \( n \), then \( 2^{d}-1 \) divides \( 2^{n}-1 \).-/
theorem number_theory_4810 (d n : ℕ) (_ : 0 < d) (h₁ : 0 < n) (h₂ : d ∣ n) :
    (2^d : ℤ) - 1 ∣ (2^n - 1) := by
  -- suppose n=dk
  rcases h₂ with ⟨k, rfl⟩
  -- rewrite 2^n to (2^d)^k
  rw [pow_mul]
  -- exact `sub_one_dvd_pow_sub_one` in Mathlib
  exact sub_one_dvd_pow_sub_one ((2^d) : ℤ) k
