import Mathlib

/- ## Task 20/81

Determine all natural numbers $n$ for which $n^{3}+1=4 p$ holds; here $p$ denotes a prime number. -/

-- lemma that if n^3 + 1 in modulo 4, then n = 3, proof by brute force on modulo values
lemma l_pow_three_add_one_mod_four (n : ZMod 4) (h : n^3 + 1 = 0) : n = 3 := by
  fin_cases n
  all_goals simp at h ⊢
  all_goals norm_cast at h

-- lemma that if n = 3 in modulo 4 then n = 4 * k + 3
lemma l_mod_four_eq_mul_add (n : ℕ) (h : (n : ZMod 4) = 3) : ∃ k, n = 4 * k + 3 := by
  rw [show (3 : ZMod 4) = ↑(3 : ℕ) by norm_cast] at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  simp at h
  use n / 4
  rw [← h]
  exact Eq.symm (Nat.div_add_mod n 4)

theorem number_theory_159190 (n : ℕ) :
    (∃ p, Nat.Prime p ∧ n^3 + 1 = 4 * p) ↔ n = 3 := by
  constructor
  -- first proving n = 3
  . rintro ⟨p, hp, hpn⟩
    -- we have n^3 + 1 = 0 in modulo 4
    have h_n_pow_three_mod_four : (n : ZMod 4)^3 + 1 = 0 := by
      norm_cast
      rw [hpn]
      push_cast
      rw [show (4 : ZMod 4) = 0 by norm_cast]
      simp
    -- so by lemma n = 3 in modulo 4
    have h_n_mod_four : (n : ZMod 4) = 3 := by
      apply l_pow_three_add_one_mod_four _ h_n_pow_three_mod_four
    -- again by lemma n = 4 * k + 3, plug in
    obtain ⟨k, hk⟩ := l_mod_four_eq_mul_add n h_n_mod_four
    rw [hk] at hpn
    ring_nf at hpn
    -- equation becomes following
    replace hpn : (k + 1) * (16 * k^2 + 20 * k + 7) = p := by linarith
    -- since p is prime, k + 1 = 1 or k + 1 = p
    have h_k_add_one_dvd_p : k + 1 ∣ p := by simp [← hpn]
    obtain h | h := Nat.Prime.eq_one_or_self_of_dvd hp (k+1) h_k_add_one_dvd_p
    -- first case gives n = 3
    . linarith
    -- in second case, we get following expression,factoring, both are untrue in natural numbers, as none can be 0
    . rw [h, Nat.mul_eq_left (hp.ne_zero)] at hpn
      replace hpn : (4 * k + 3) * (2 * k + 1) = 0 := by linarith
      simp at hpn
  -- to prove n = 3 satisfies condition, use 7 as the prime
  . rintro rfl
    use 7
    norm_num