import Mathlib
/- Let $[x]$ denote the greatest integer not exceeding $x$. Let $M$ be a positive integer. Find the last two digits of the sum $\left[\frac{2^0}{3}\right]+\left[\frac{2^1}{3}\right]+\left[\frac{2^{2}}{3}\right]+\cdots+\left[\frac{2^{200M+14}}{3}\right]$. Show the answer is 15. -/
theorem number_theory_637578 (m : ℕ) (hm : m > 0) : (∑ i in Finset.range (200 * m + 15), (2 ^ i / 3)) % 100 = 15:= by

  -- Main lemma: For any natural number n,
  -- 3 * (sum of [2^i/3] from i=0 to 2n) + 3n + 2 = 2^(2n+1)
  have h1 : ∀ n : ℕ, 3 * (∑ i in Finset.range (2 * n + 1), (2 ^ i / 3)) + 3 * n + 2 = 2 ^ (2 * n + 1):= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 3 * (∑ x ∈ Finset.range (2 * n + 1), 2 ^ x / 3 + 2 ^ (2 * n + 1) / 3 + 2 ^ (2 * n + 2) / 3) + 3 * (n + 1) + 2 = 3 * (∑ x ∈ Finset.range (2 * n + 1), 2 ^ x / 3) + 3 * n + 2 + 3 * (2 ^ (2 * n + 1) / 3 + 2 ^ (2 * n + 2) / 3) + 3 by ring, ih]

      -- Prove that 2^(2n) ≡ 1 (mod 3)
      have g : 2 ^ (2 * n) ≡ 1 [MOD 3]:= by
        rw [show 2 ^ (2 * n) = (2 ^ 2) ^ n by exact Nat.pow_mul 2 2 n]
        simp
        have g : 4 ≡ 1 [MOD 3]:= by rfl
        replace g : 4 ^ n ≡ 1 ^ n [MOD 3]:= by exact Nat.ModEq.pow n g
        simp at g
        exact g
      have g1 : 2 ^ (2 * n) > 0:= by positivity
      replace g : 3 ∣ 2 ^ (2 * n) - 1:= by
        replace g1 : 2 ^ (2 * n) ≥ 1:= by omega
        exact (Nat.modEq_iff_dvd' g1).mp (id (Nat.ModEq.symm g))
      rcases g with ⟨k, hk⟩
      replace hk : 2 ^ (2 * n) = 3 * k + 1:= by omega
      rw [show 2 ^ (2 * n + 1) = 6 * k + 2 by rw [show 2 ^ (2 * n + 1) = 2 * 2 ^ (2 * n) by ring] ; rw [hk] ; ring_nf]
      rw [show 2 ^ (2 * n + 2) = 12 * k + 4 by rw [show 2 ^ (2 * n + 2) = 4 * 2 ^ (2 * n) by ring] ; rw [hk] ; ring_nf]
      rw [show 2 ^ (2 * n + 1 + 1 + 1) = 24 * k + 8 by rw [show 2 ^ (2 * n + 1 + 1 + 1) = 8 * 2 ^ (2 * n) by ring] ; rw [hk] ; ring_nf]
      omega

  -- Apply the lemma with n = 100m + 7
  specialize h1 (100 * m + 7)
  rw [show 2 * (100 * m + 7) + 1 = 200 * m + 15 by omega] at h1
  have g2 : 15 = 15 % 100:= by rfl
  rw [g2]
  set t:= ∑ i in Finset.range (200 * m + 15), 2 ^ i / 3
  clear_value t
  clear g2

  -- Prove that 2^10 ≡ 24 (mod 100)
  have g2 : 2 ^ 10 ≡ 24 [MOD 100]:= by rfl
  rw [show 200 * m + 15 = 10 * (20 * m + 1) + 5 by ring] at h1
  rw [show 2 ^ (10 * (20 * m + 1) + 5) = 32 * 2 ^ (10 * (20 * m + 1)) by ring_nf] at h1
  rw [show 2 ^ (10 * (20 * m + 1)) = (2 ^ 10) ^ (20 * m + 1) by exact Nat.pow_mul 2 10 (20 * m + 1)] at h1
  set s:= 2 ^ 10
  clear_value s
  have g1:= g2

  -- Prove properties about modular arithmetic
  replace g2 : s ^ 2 ≡ 24 ^ 2 [MOD 100]:= by exact Nat.ModEq.pow 2 g2
  replace g2 : s ^ 2 ≡ 76 [MOD 100]:= by exact g2
  replace g2 : ∀ k : ℕ, (s ^ 2) ^ (k + 1) ≡ 76 [MOD 100]:= by
    intro k
    induction k with
    | zero =>
      simp
      exact g2
    | succ k ih =>
      rw [show (s ^ 2) ^ (k + 1 + 1) = (s ^ 2) ^ (k + 1) * s ^ 2 by ring_nf]
      replace g2:= Nat.ModEq.mul ih g2
      exact g2
  specialize g2 (10 * m - 1)
  rw [show 10 * m - 1 + 1 = 10 * m by omega] at g2
  ring_nf at g2
  replace g1:= Nat.ModEq.mul g1 g2
  rw [show s * s ^ (m * 20) = s ^ (20 * m + 1) by ring_nf] at g1
  replace g1 : s ^ (20 * m + 1) ≡ 24 [MOD 100]:= by exact g1
  clear g2
  replace g1 : 32 * s ^ (20 * m + 1) ≡ 32 * 24 [MOD 100]:= by exact Nat.ModEq.mul rfl g1
  rw [←h1] at g1
  replace g1 : 67 * (3 * t + 3 * (100 * m + 7) + 2) ≡ 67 * (32 * 24) [MOD 100]:= by exact Nat.ModEq.mul rfl g1
  rw [show 67 * (3 * t + 3 * (100 * m + 7) + 2) = t + 67 * 23 + 100 * (2 * t + 201 * m) by ring_nf] at g1

  -- Final steps to prove the sum modulo 100 equals 15
  have g2 : 100 * (2 * t + 201 * m) ≡ 0 [MOD 100]:= by
    suffices 100 ∣ 100 * (2 * t + 201 * m) by exact Nat.modEq_zero_iff_dvd.mpr this
    simp
  replace g2 : t + 67 * 23 + 100 * (2 * t + 201 * m) ≡ t + 67 * 23 + 0 [MOD 100]:= by exact Nat.ModEq.add rfl g2
  set p:= t + 67 * 23 + 100 * (2 * t + 201 * m)
  clear_value p
  simp at g1 g2
  replace g2 : t + 1541 ≡ 51456 [MOD 100]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g1)) g2)
  simp at g2
  replace g2 : t + 1541 ≡ 56 [MOD 100]:= by exact g2
  replace g2 : t + 1541 + 59 ≡ 56 + 59 [MOD 100]:= by exact Nat.ModEq.add g2 rfl
  ring_nf at g2
  replace g2 : 1600 + t ≡ 15 [MOD 100]:= by exact g2
  rw [←g2]
  have g1 : 1600 ≡ 0 [MOD 100]:= by rfl
  replace g1 : 1600 + t ≡ 0 + t [MOD 100]:= by exact Nat.ModEq.add g1 rfl
  simp at g1
  rw [g1]
