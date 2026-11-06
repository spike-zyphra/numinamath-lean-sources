import Mathlib

/- Let  $p$  be a prime number and let  $m$  and  $n$  be positive integers with  $p^2 + m^2 = n^2$ .
Prove that  $m> p$ . -/
theorem number_theory_8970 {p m n : ℕ} (hp : Nat.Prime p)
  (hm : 0 < m) (hn : 0 < n) (h : p^2 + m^2 = n^2) :
  m > p := by

    -- rewrite the equation:
    -- p^2 = n^2 - m^2 = (n + m) * (n - m)
    replace h : p^2 = n^2 - m^2 := by omega
    replace h : p^2 = (n + m) * (n - m) := by rwa [Nat.sq_sub_sq] at h

    -- Thus n - m is a power of p, say p^k.
    obtain ⟨k, kle2, hk⟩ : ∃ k ≤ 2, n - m = p^k := by
      rw [← Nat.dvd_prime_pow hp, h]
      apply Nat.dvd_mul_left

    -- simple lemmas:
    -- n - m < n + m
    -- n - m > 0
    have h1 : n - m < n + m := by omega
    have h2 : n - m ≠ 0 := by
      intro s
      rw [s] at h
      simp at h
      have : p > 0 := Nat.Prime.pos hp
      omega
    replace h2 : n - m > 0 := by omega

    -- We obtain p^k * p^k < p^2 by combining the equalities with the equation.
    have h3 : p^k * p^k < p^2 := by
      have : (n - m) * (n - m) < (n + m) * (n - m) := Nat.mul_lt_mul_of_pos_right h1 h2
      rw (config := {occs := .pos [1, 2]}) [hk] at this
      rwa [h]

    -- Therefore, k must be 0.
    replace h3 : p^(k+k) < p^2 := by rwa [Nat.pow_add]
    have h4 : k+k < 2 := (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt hp)).1 h3
    have keq0 : k = 0 := by omega

    -- And n - m = 1, n + m = p^2.
    have h5 : n - m = 1 := by rwa [keq0, Nat.pow_zero] at hk
    clear k hk h1 h2 h3 h4 keq0 kle2
    have h6 : n + m = p^2 := by
      rw [h5] at h
      simp at h
      exact Eq.symm h

    -- Now we only need to prove p^2 > 2p+1.
    suffices _ : 2 * m + 1 > 2 * p + 1 by omega
    have h7 : 2 * m + 1 = p^2 := by omega
    rw [h7]

    -- If p = 2, then 2 * m + 1 = 4, which is impossible. Thus p ≥ 3.
    have pge3 : p ≥ 3 := by
      have pge2 : p ≥ 2 := Nat.Prime.two_le hp
      suffices _ : p ≠ 2 by omega
      intro peq2
      have h8 : 2 * m + 1 = 4 := by rwa [peq2] at h7
      omega

    -- p^2 ≥ 3p ≥ 2p+1.
    have h8 : p * 3 ≤ p^2 := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul_left p pge3
    omega
