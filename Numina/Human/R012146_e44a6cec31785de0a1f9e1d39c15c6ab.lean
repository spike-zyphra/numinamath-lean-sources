import Mathlib

/- 7. A natural number $N$ ends in ...70, and it has exactly 72 natural divisors (including 1 and itself). How many natural divisors does the number 80N have? ANSWER: 324. -/
theorem number_theory_188876 {N : ℕ} (hN : N % 100 = 70) (hN1 : N.divisors.card = 72) :
    (80 * N).divisors.card = 324 := by
-- have that 10 | N since (N % 100 = 70)
-- and take M that N = 10 M
  have ⟨M, hM⟩ : 10 ∣ N := by
    apply (Nat.dvd_mod_iff (by norm_num : 10 ∣ 100)).1
    rw [hN]
    norm_num
-- from N % 100 = 70 deduce that M % 70 = 10,
-- then deduce that M is coprime with 10
  have hCoprime : Nat.Coprime 10 M := by
-- Nat.mul_mod_mul_left tell us (a * b) % (a * c) = b % c,
-- here a = 10, b = M, c = 10
    have H := Nat.mul_mod_mul_left 10 M 10
    rw [←hM, hN] at H
    rw [(by norm_num : 70 = 10 * 7)] at H
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 10) at H
-- now get M % 10 = 7,
-- then apply Nat.gcd_rec : gcd 10 M = gcd (M % 10) 10
    unfold Nat.Coprime
    rw [Nat.gcd_rec, ←H]
    norm_num
-- Nat.Coprime.card_divisors_mul tells us
-- (a*b).divisors.card = a.divisors.card * b.divisors.card if a and b are coprime.
-- so from n = 10 * m we can compute m.divisors.card
  have hMdivisorcard : M.divisors.card = 18 := by
    have H := Nat.Coprime.card_divisors_mul hCoprime
    rw [←hM, hN1] at H
    rw [(by decide : (Nat.divisors 10).card = 4)] at H
    omega
-- 80 N = 800 M, and 800 is coprime with M
-- from the same reason we can get the number of divisors of 800 M.
  rw [hM]
  rw [(by omega: 80 * (10 * M) = 800 * M)]
  apply (Nat.Coprime.pow_left 5) at hCoprime
  apply (Nat.Coprime.of_dvd_left (by omega : 800 ∣ 10 ^ 5)) at hCoprime
  rw [Nat.Coprime.card_divisors_mul hCoprime]
  rw [hMdivisorcard, (by decide : (Nat.divisors 800).card = 18)]