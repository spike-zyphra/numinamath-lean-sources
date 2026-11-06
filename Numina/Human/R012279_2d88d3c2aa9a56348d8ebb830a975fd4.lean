import Mathlib

/-- The least common multiple of a positive integer n and 18 is 180,
    and the greatest common divisor of n and 45 is 15.
    What is the sum of the digits of n?
    (A) 3(B) 6(C) 8(D) 9(E) 12 -/
theorem number_theory_93816 {n : ℕ} (hn : n ≠ 0) (h1 : Nat.lcm n 18 = 180) (h2 : Nat.gcd n 45 = 15) :
    (Nat.digits 10 n).sum = 6 := by
  -- We have 15 | n, since it is the gcd of n and 45.
  have n15 : 15 ∣ n := by
    trans n.gcd 45
    · rw[h2]
    · exact Nat.gcd_dvd_left n 45
  -- We do not have 9 | n, since it divides 45, but not the gcd of n with it.
  have n9 : ¬ (9 ∣ n) := by
    intro h
    have : 9 ∣ 45 := by norm_num
    have : 9 ∣ n.gcd 45 := Nat.dvd_gcd h this
    rw[h2] at this
    contradiction

  obtain ⟨k,rfl⟩ : 30 ∣ n := by
    -- Write n = 15k,
    obtain ⟨k,rfl⟩ := n15
    change ((3 * 5)* k).lcm (3 * 6) = 180 at h1
    rw[mul_assoc, Nat.lcm_mul_left] at h1
    -- then lcm(5k,6) = lcm(15k,18)/3 = 60.
    have lcm : (5 * k).lcm 6 = 60 := by linarith
    -- Hence, 5k * 6 = 60 * gcd(5k,6)
    have := Nat.gcd_mul_lcm (5 * k) 6
    rw[lcm] at this
    -- such that k = 2 gcd(5k, 6)
    have : 2 * (5 * k).gcd 6 = k := by linarith
    rw[← this]
    -- and n = 15k = 30 gcd(5k,6) must be a multiple of 30.
    exists (5 * k).gcd 6
    ring
  -- From here on, write n = 30k.
  -- Then, 540k = gcd(30k, 18) lcm(30k,18) = 180 gcd(30k, 18) = 1080 gcd(5k, 3).
  have := Nat.gcd_mul_lcm (30 * k) 18
  rw[h1] at this
  convert_to (6 * (5 * k)).gcd (6 * 3) * 180 = 30 * 18 * k at this
  · ring_nf
  · ring_nf
  · rw[Nat.gcd_mul_left, Nat.Coprime.gcd_mul_left_cancel _ (by norm_num)] at this
    -- Hence, k = 2 gcd(5k, 3),
    have : 2 * k.gcd 3 = k := by linarith
    -- but 3 cannot be a divisor of k since 9 is not a divisor of n,
    have not3 : ¬ 3 ∣ k := by
      rintro ⟨i, rfl⟩
      apply n9
      exists 10 * i
      ring
    -- so 3 and 5k are coprime
    rw[← Nat.Prime.coprime_iff_not_dvd (by norm_num)] at not3
    -- and k = 2, such that n = 60.
    rw[not3.symm] at this
    rw[← this]
    -- But the sum of digits of 60 is 6.
    simp