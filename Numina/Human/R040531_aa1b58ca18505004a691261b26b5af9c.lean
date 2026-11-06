import Mathlib
open Nat

/-20. Find the last two digits of $2011^{\left(2010^{2000)}\right.}$.-/
theorem number_theory_600015 : (2011^(2010^2000)) % 100 = 1 := by
  -- Prove $2011 ≡ 11 (mod 100)$.
  have h1 : 2011 ≡ 11 [MOD 100] := by
    have : 2011 = 2000 + 11 := by norm_num
    rw [this]
    norm_num
    rfl
  -- Prove $2011^(2010^2000) ≡ 11^(2010^2000) (mod 100)$.
  have h2 : 2011^(2010^2000) ≡ 11^(2010^2000) [MOD 100] := by
    apply Nat.ModEq.pow (2010^2000) h1
  -- Prove $11^10 ≡ 1 (mod 100)$.
  have h3 : 11^10 ≡ 1 [MOD 100] := by
    have h₁: 11^10 = 25937424601 := rfl
    have h₂: 25937424601 = 100 * 259374246 + 1 := rfl
    rw [h₁,h₂]
    norm_num
    rfl
  -- Prove $2010^2000$ is divisible by $10$.
  have h4 : 10 ∣ 2010^2000 := by
    have : 10 ∣ 2010 := by norm_num
    apply dvd_pow this (by norm_num)
  -- Express $2010^2000 = 10 * k$ for some $k$.
  have h5 : ∃ k, 2010^2000 = 10 * k := by
    exact exists_eq_mul_right_of_dvd h4
  -- Rewrite $11^(2010^2000)$.
  cases h5 with | intro k hk =>
  have h6 : 11^(2010^2000) = 11^(10 * k) := by rw [hk]
  have h7 : 11^(10 * k) = (11^10)^k := by rw [pow_mul]
  have h8 : 11^(10 * k) ≡ (11^10)^k [MOD 100] := by rw [h7]
  have h9 : (11^10)^k ≡ 1^k [MOD 100] := by
    apply Nat.ModEq.pow k h3
  have h10 : 1^k = 1 := by norm_num
  have h11 : (11^10)^k ≡ 1 [MOD 100] := by rwa [h10] at h9
  have h12 : 11^(10 * k) ≡ 1 [MOD 100] := by rwa [h7]
  -- Combine results.
  have h13 : 11^(2010^2000) ≡ 1 [MOD 100] := by rwa [← hk] at h12
  have h14 : 2011^(2010^2000) ≡ 1 [MOD 100] := Nat.ModEq.trans h2 h13
  rw [Nat.ModEq] at h14
  exact h14
