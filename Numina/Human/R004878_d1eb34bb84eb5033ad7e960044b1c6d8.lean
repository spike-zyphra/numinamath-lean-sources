import Mathlib

/- Consider the assertion that for each positive integer $n \geq 2$, the remainder upon dividing $2^{2^{n}}$ by $2^{n}-1$ is a power of 4 . Either prove the assertion or find (with proof) a counterexample. -/
theorem number_theory_604405 (n : ℕ) (hn : 2 ≤ n) :
    (∃ k, (2^(2^n)) % (2^n - 1) = 4^k)
    → n ≠ 25 /- $n = 25$ is a counterexample. -/
    := by

  by_contra h
  push_neg at h
  obtain ⟨ h', h25 ⟩ := h
  obtain ⟨ k, hk ⟩ := h'
  rw [h25] at hk
  norm_num at hk
  by_cases g : k < 3
  . have : 4 ^ k < 4 ^ 3 := by
      rw [Nat.pow_lt_pow_iff_right]
      . exact g
      . norm_num
    revert this
    simp
    rw [← hk]
    norm_num
  . by_cases g' : k = 3
    . aesop
    . have : 4 ≤ k := by omega
      have : 4 ^ 4 ≤ 4 ^ k := by
        rw [Nat.pow_le_pow_iff_right]
        . exact this
        . norm_num
      revert this
      simp
      rw [← hk]
      trivial