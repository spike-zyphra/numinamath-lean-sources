import Mathlib

/-Find all natural integers  $m, n$  such that  $m, 2+m, 2^n+m, 2+2^n+m$  are all prime numbers-/
theorem number_theory_8670 (p n : ℕ)(hp : Nat.Prime p)
(h1 : Nat.Prime (p + 2)) (h2 : Nat.Prime (2 ^ n + p))(h3 : Nat.Prime (2 + 2 ^ n + p)) :
p = 3 ∧ (n = 1 ∨ n = 3) := by
-- Prove that $p$ can't be $2$
  by_cases h' : p = 2
  · rw [h'] at h1; simp at h1; contradiction
  push_neg at h'
-- Prove that $n$ can't be $0$
  by_cases h0 : n = 0
  · rw [h0] at h2; simp at h2
    rw [Nat.prime_def_lt''] at hp; rcases hp with ⟨hp1, hp2⟩
    have w1 := Nat.mod_add_div p 2
    have w2 := Nat.mod_lt p (show 0<2 by norm_num)
    nth_rw 2 [show 2=1+1 by norm_num] at w2; rw [Nat.lt_add_one_iff_lt_or_eq] at w2
    rcases w2 with w2l | w2r
    · simp at w2l; rw [w2l] at w1; simp at w1
      have x1 : 2 ∣ p := by use p/2; symm; assumption
      have x2 := hp2 2 x1
      simp at x2; symm at x2; contradiction
    rw [w2r] at w1
    have y1 : 2 ∣ 1+p := by use 1+p/2; nth_rw 1 [← w1]; ring
    rcases Nat.prime_def_lt''.mp h2 with ⟨h2l,h2r⟩
    have := h2r 2 y1
    simp at this; rw [this] at hp1; linarith
  push_neg at h0
-- Prove that $p$ can't be greater or equal to $5$
  by_cases h'' : 5 ≤ p
-- Use division with remainder on $p$ and prove by cases $p % 3=2$, $p % 3=1$ and $p % 3=0$
  have r1 := Nat.mod_add_div p 3
  have r2 := Nat.mod_lt p (show 0<3 by norm_num)
  nth_rw 2 [show 3=2+1 by norm_num] at r2; rw [Nat.lt_add_one_iff_lt_or_eq] at r2
  rcases r2 with hrr | hll
  · rw [show 2=1+1 by norm_num, Nat.lt_add_one_iff_lt_or_eq] at hrr
    rcases hrr with hr | hl
    · rw [show 1=0+1 by norm_num, Nat.lt_add_one_iff_lt_or_eq] at hr
      rcases hr with h'r | h'l
      · contradiction
-- Case $p % 3=0$, we prove that $p=3$, which contradicts to the assumption that $p$ is greater or equal to $5$
      · rw [h'l] at r1; simp at r1;
        have : 3 ∣ p := by use (p / 3); symm; assumption
        have t1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this
        rw [← t1] at h''; linarith
-- Case $p % 3=1$, we prove that $p=1$, which contradicts to the assumption that $p$ is greater or equal to $5$
    · rw [hl] at r1
      have : 3 ∣ p + 2 := by use (p/3+1); nth_rw 1 [← r1]; ring
      have s1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h1).mp this
      simp at s1; linarith
-- Case $p % 3=2$, we prove that $3$ divides $2^n+p$ or $2+2^n+p$
  · rw [hll] at r1
    let k := p/3
    have u1 : p = 3 * k + 2 := by simp only [k]; symm; rw [add_comm]; assumption
    have u2 : 3 ∣ 2 ^ n + p ∨ 3 ∣ 2 + 2 ^ n + p := by
-- Use division with remainder on $2^n$ and prove by cases $2^n % 3=2$, $2^n % 3=1$ and $2^n % 3=0$
      have v1 := Nat.mod_add_div (2^n) 3
      have v2 := Nat.mod_lt (2^n) (show 0<3 by norm_num)
      nth_rw 2 [show 3=2+1 by norm_num] at v2; rw [Nat.lt_add_one_iff_lt_or_eq] at v2
      rcases v2 with h'rr | h'll
      · nth_rw 2 [show 2=1+1 by norm_num]; rw [Nat.lt_add_one_iff_lt_or_eq] at h'rr
        rcases h'rr with h''r | h''l
        · rw [show 1=0+1 by norm_num, Nat.lt_add_one_iff_lt_or_eq] at h''r
          rcases h''r with h'''r | h'''l
          · contradiction
-- Case $2^n % 3=0$
          · rw [h'''l] at v1; simp at v1
            have w1 : 3 ∣ 2 ^ n := by use (2 ^ n / 3); symm; assumption
            have w2 := (Prime.dvd_pow_iff_dvd (Nat.prime_iff.mp Nat.prime_three) h0).mp w1
            contradiction
-- Case $2^n % 3=1$
        · left; rw [h''l] at v1; use k+(2^n)/3+1
          nth_rw 1 [← v1]; rw [u1]; ring
-- Case $2^n % 3=2$
      · right; rw [h'll] at v1; use k+(2^n)/3+2
        nth_rw 1 [← v1]; rw [u1]; ring
    rcases u2 with u2l | u2r
-- Case $3$ divides $2^n+p$
    · have z1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).mp u2l
      have : p ≤ 3 := by rw [z1]; simp
      linarith
-- Case $3$ divides $2+2^n+p$
    · have z2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h3).mp u2r
      have : p ≤ 3 := by rw [z2]; simp
      linarith
-- Prove that $p$ equals $3$ since $p$ is prime and less than $5$
  push_neg at h''; simp [Nat.lt_iff_add_one_le] at h''
  cases h'' with
  | refl => contradiction
  | step h'' =>
    simp at h''; cases h'' with
-- Case $m$ equals $3$, prove that $n$ has to be $1$ or $3$
    | refl =>
      simp_all; rw [add_comm, ← add_assoc] at h3; simp at h3
-- Split to the case when $n$ is even or odd
      rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
-- Case $n$ is even, we prove that $3$ divides $5+2^n$ contradicting to the fact that $5+2^n$ is prime
      · rw [hk, pow_mul, show 2^2=4 by simp] at h3
        have cr1 : 4 ^ k ≡ 1 ^ k [MOD 3] := by
          apply Nat.ModEq.pow; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        have : 3 ∣ 5 + 4 ^ k := by
          rw [← Nat.modEq_zero_iff_dvd]
          have : 0 ≡ 2 + 1 [MOD 3] := by simp; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
          suffices cr3 : 5 + 4 ^ k ≡ 2 + 1 [MOD 3]
          exact Nat.ModEq.trans cr3 (Nat.ModEq.comm.mp this)
          apply Nat.ModEq.add; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
          simp at cr1; assumption
        rw [Nat.prime_dvd_prime_iff_eq] at this
        have : 0 < 4 ^ k := by apply Nat.pow_pos; norm_num
        linarith; assumption; assumption
-- Case $n$ is odd and equals $2k+1$, split to the case when $k$ is even or odd
      rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
      · simp [hk] at h2 h3; simp [hk]; simp [ht]; simp [ht] at h2 h3; ring_nf at h2 h3
        have cr1 :  2 ^ (t * 4) * 2 ≡ 2 [MOD 5] := by
          nth_rw 2 [mul_comm]; rw [pow_mul, show 2^4=16 by simp]
          nth_rw 2 [show 2=1*2 by simp]; apply Nat.ModEq.mul
          rw [show 1=1^t by simp]; apply Nat.ModEq.pow
          rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char; rfl
        have dvd5 : 5 ∣ 3 + 2 ^ (t * 4) * 2 := by
          rw [← Nat.modEq_zero_iff_dvd]
          have : 0 ≡ 3 + 2 [MOD 5] := by simp; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
          suffices cr3 : 3 + 2 ^ (t * 4) * 2 ≡ 3 + 2 [MOD 5]
          exact Nat.ModEq.trans cr3 (Nat.ModEq.comm.mp this)
          apply Nat.ModEq.add; rw [← ZMod.eq_iff_modEq_nat]; assumption
        rw [Nat.prime_dvd_prime_iff_eq] at dvd5; by_cases h: 1 ≤ t
        · have : 2 ≤ 2 ^ (t * 4) := by
            apply Nat.le_self_pow; linarith
          linarith
        simp at h; assumption; assumption; assumption
      simp [hk] at h2 h3; simp [hk]; simp [ht] at h2 h3; simp [ht]; ring_nf at h2 h3
-- Split to the cases when $t%3$ is $0$, $1$ or $2$
      have tm3 := Nat.mod_add_div t 3
      have hr : t % 3 < 3 := by apply Nat.mod_lt; norm_num
      simp [Nat.lt_iff_add_one_le] at hr; rw [Nat.le_iff_lt_or_eq] at hr
      cases hr; rename_i hr
      simp [Nat.lt_iff_add_one_le] at hr; rw [Nat.le_iff_lt_or_eq] at hr
-- Case $t%3$ is $0$, we prove that $13$ divides $5+2^(t*4)*8$, therefore as prime numbers, they must be equal
      cases hr; rename_i hr; simp at hr; rw [hr] at tm3; simp at tm3
      rw [← tm3] at h3; nth_rw 2 [mul_comm] at h3; rw [← mul_assoc, pow_mul] at h3
      simp at h3
-- Apply Fermat Little theorem to get the following congruence relation
      have cr1 := Nat.ModEq.pow_totient (show (Nat.Coprime 2 13) by norm_num)
      rw [Nat.totient_prime] at cr1; simp at cr1
      have d13 : 13 ∣ 5 + (2 ^ 12) ^ (t / 3) * 8 := by
        rw [← Nat.modEq_zero_iff_dvd]
        have : 0 ≡ 5 + 8 [MOD 13] := by simp; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        suffices cr3 : 5 + (2 ^ 12) ^ (t / 3) * 8 ≡ 5 + 8 [MOD 13]
        exact Nat.ModEq.trans cr3 (Nat.ModEq.comm.mp this)
        apply Nat.ModEq.add; rfl; nth_rw 2 [show 8=1*8 by simp]
        apply Nat.ModEq.mul; rw [show 1=1^(t/3) by simp]; apply Nat.ModEq.pow
        simp; assumption; rfl
      simp at d13; rw [Nat.prime_dvd_prime_iff_eq] at d13
      by_cases h' : 3 ≤ t
      · have : 4096 ≤ 4096 ^ (t / 3) := by
          apply Nat.le_self_pow; rw [← Nat.pos_iff_ne_zero]
          apply Nat.div_pos; assumption; norm_num
        linarith
      simp at h'; rw [← hr]; symm; rw [Nat.mod_eq_iff_lt]; assumption
      norm_num; norm_num; assumption; norm_num
-- Case $t%3$ is $1$, we prove that $7$ divides divides $5+2^(t*4)*8$, therefore as prime numbers, they must be equal
      rename_i hr; rw [hr] at tm3; rw [← tm3] at h3; ring_nf at h3
      nth_rw 2 [mul_comm] at h3; rw [mul_comm, pow_mul] at h3; simp at h3
      have cr1 : 4096 ≡ 1 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
      have d7 : 7 ∣ 5 + 128 * 4096 ^ (t / 3) := by
        rw [← Nat.modEq_zero_iff_dvd]
        have : 0 ≡ 5 + 2 [MOD 7] := by simp; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        suffices cr3 : 5 + 128 * 4096 ^ (t / 3) ≡ 5 + 2 [MOD 7]
        exact Nat.ModEq.trans cr3 (Nat.ModEq.comm.mp this)
        apply Nat.ModEq.add; rfl; rw [show 2=2*1 by simp]
        apply Nat.ModEq.mul; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        rw [show 1=1^(t/3) by simp]; apply Nat.ModEq.pow; assumption
      rw [Nat.prime_dvd_prime_iff_eq] at d7; by_cases h' : 3 ≤ t
      · have : 4096 ≤ 4096 ^ (t / 3) := by
          apply Nat.le_self_pow; rw [← Nat.pos_iff_ne_zero]
          apply Nat.div_pos; assumption; norm_num
        linarith
      simp at h'; have : 1 ≤  4096 ^ (t / 3) := by linarith
      linarith; norm_num; assumption
-- Case $t%3$ is $2$, we prove that $7$ divides divides $3+2^(t*4)*8$, therefore as prime numbers, they must be equal
      rename_i hr; rw [hr] at tm3; rw [← tm3] at h2; ring_nf at h2
      nth_rw 2 [mul_comm] at h2; rw [mul_comm, pow_mul] at h2; simp at h2
      have cr2 : 4096 ≡ 1 [MOD 7] := by rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
      have d7 : 7 ∣ 3 + 2048 * 4096 ^ (t / 3) := by
        rw [← Nat.modEq_zero_iff_dvd]
        have : 0 ≡ 3 + 4 [MOD 7] := by simp; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        suffices cr3 : 3 + 2048 * 4096 ^ (t / 3) ≡ 3 + 4 [MOD 7]
        exact Nat.ModEq.trans cr3 (Nat.ModEq.comm.mp this)
        apply Nat.ModEq.add; rfl; rw [show 4=4*1 by simp]
        apply Nat.ModEq.mul; rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
        rw [show 1=1^(t/3) by simp]; apply Nat.ModEq.pow; assumption
      rw [Nat.prime_dvd_prime_iff_eq] at d7; by_cases h' : 3 ≤ t
      · have : 4096 ≤ 4096 ^ (t / 3) := by
          apply Nat.le_self_pow; rw [← Nat.pos_iff_ne_zero]
          apply Nat.div_pos; assumption; norm_num
        linarith
      simp at h'; have : 1 ≤ 4096 ^ (t / 3) := by linarith
      linarith; norm_num; assumption
    | step hst =>
      simp at hst; rw [Nat.prime_def_lt] at hp; rcases hp with ⟨⟩
      have : p = 2 := by linarith
      contradiction