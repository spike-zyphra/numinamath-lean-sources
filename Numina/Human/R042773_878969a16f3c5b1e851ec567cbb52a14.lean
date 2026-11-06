import Mathlib

/- The difference between the squares of two different primes is 1488. Given both primes are less than 50, find the primes.

Note: Submit the numbers in either order separated by a comma. -/
theorem algebra_20698 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hdiff : p ^ 2 - q ^ 2 = 1488) (h50 : p < 50 ∧ q < 50) : p = 43 ∧ q = 19 := by
        -- 证明 p > q
        have h1 : p ^ 2 - q ^ 2 > 0:= by omega
        replace h1 : p ^ 2 > q ^ 2:= by exact Nat.lt_of_sub_eq_succ hdiff
        replace h1 : p > q:= by exact lt_of_pow_lt_pow_left' 2 h1
        -- 证明 q ≠ 2
        have hqne2 : q ≠ 2:= by
            by_contra H
            have hpne2 : p ≠ 2:= by
                by_contra!
                omega
            have hpodd : Odd p:= Nat.Prime.odd_of_ne_two hp hpne2
            rw [H] at hdiff
            replace hpodd : Odd (p ^ 2):= by exact Odd.pow hpodd
            rw [H] at h1
            replace h1 : p ^ 2 > 2 ^ 2:= by exact Nat.lt_of_sub_eq_succ hdiff
            replace hdiff : p ^ 2 - 2 ^ 2 + 2 ^ 2 = 1488 + 2 ^ 2:= by omega
            rw [show  p ^ 2 - 2 ^ 2 + 2 ^ 2 = p ^ 2 by refine Nat.sub_add_cancel (by omega)] at hdiff
            simp at hdiff
            rw [hdiff] at hpodd
            trivial
        clear hne
        rcases h50 with ⟨hp50, hq50⟩
        -- zify 后进行因式分解
        zify at hdiff
        rw [show (↑(p ^ 2 - q ^ 2) : ℤ) = ↑ (p ^ 2) - ↑(q ^ 2) by refine Int.ofNat_sub (by omega)] at hdiff
        rw [show (↑(p ^ 2) : ℤ) = (↑p) ^ 2 by norm_cast] at hdiff
        rw [show (↑(q ^ 2) : ℤ) = (↑q) ^ 2 by norm_cast] at hdiff
        rw [show (↑p : ℤ) ^ 2 - ↑q ^ 2 = (↑p - ↑q) * (↑p + ↑q) by ring] at hdiff
        rw [show (1488 : ℤ) = 2 ^ 4 * 3 * 31 by omega] at hdiff
        -- 证明 p ≠ 2
        have hpne2 : p ≠ 2:= by
            by_contra!
            have hqge2 : q ≥ 2:= by exact Nat.Prime.two_le hq
            omega
        -- 证明 p - q, p + q 均为偶数
        have hpodd : Odd p:= Nat.Prime.odd_of_ne_two hp hpne2
        have hqodd : Odd q:= Nat.Prime.odd_of_ne_two hq hqne2
        replace hpodd : Odd (↑p : ℤ):= by exact (Int.odd_coe_nat p).mpr hpodd
        replace hqodd : Odd (↑q : ℤ):= by exact (Int.odd_coe_nat q).mpr hqodd
        have hpqa2 : Even ((↑p : ℤ) + ↑q):= by exact Odd.add_odd hpodd hqodd
        have hpqb2 : Even ((↑p : ℤ) - ↑q):= by exact Odd.sub_odd hpodd hqodd
        clear hpodd hqodd hpne2 hqne2
        -- 得到 31 ∣ p - q 或 31 ∣ p + q
        have h2 : (31 : ℤ) ∣ (↑p - ↑q) * (↑p + ↑q):= by omega
        replace h2 : (31 : ℕ) ∣ (p - q) * (p + q):= by
            zify
            rw [show (↑(p - q) : ℤ) = ↑p - ↑q by refine Int.ofNat_sub (by omega)]
            exact h2
        have g : Prime 31:= by refine Nat.prime_iff.mp (by decide)
        replace h2 : 31  ∣ (p - q) ∨ 31 ∣ (p + q):= by exact Prime.dvd_or_dvd g h2
        -- 分情况讨论，得到相应解
        rcases h2 with h2 | h2
        .
            by_contra!
            have h3 : (2 : ℤ) ∣ ↑p - ↑q:= by exact even_iff_two_dvd.mp hpqb2
            replace h3 : 2 ∣ p - q:= by
                zify
                rw [show (↑(p - q) : ℤ) = ↑p - ↑q by refine Int.ofNat_sub (by omega)]
                exact h3
            replace h3 : 31 * 2 ∣ p - q:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h2 h3
            simp at h3
            replace h3 : 62 ≤ p - q:= by exact Nat.le_of_dvd (by omega) h3
            zify at h3
            rw [show (↑(p - q) : ℤ) = ↑p - ↑q by refine Int.ofNat_sub (by omega)] at h3
            have h4 : q ≥ 0:= by exact Nat.zero_le q
            zify at h4
            replace h3 : 62 ≤ ↑p:= by omega
            zify at hp50
            omega
        .
            have h3 : (2 : ℤ) ∣ ↑p + ↑q:= by exact even_iff_two_dvd.mp hpqa2
            replace h3 : 2 ∣ p + q:= by
                zify
                exact h3
            replace h3 : 31 * 2 ∣ p + q:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h2 h3
            simp at h3
            have h4 : p + q < 100:= by omega
            replace h3 : ∃ k : ℕ, p + q = k * 62:= by exact exists_eq_mul_left_of_dvd h3
            rcases h3 with ⟨k, h3⟩
            have hkle2 : k < 2:= by
                by_contra!
                replace this : 124 ≤ p + q:= by omega
                omega
            have hkne0 : k ≠ 0:= by
                by_contra!
                rw [this] at h3
                omega
            have hkeq1 : k = 1:= by omega
            simp [hkeq1] at h3
            zify at h3
            simp [h3] at hdiff
            have gp : p = 43:= by omega
            have gq : q = 19:= by omega
            exact ⟨gp, gq⟩
