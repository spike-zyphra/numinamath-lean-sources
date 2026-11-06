import Mathlib

/-
a) Show that if $ a $ and $ b $ are positive integers, then $ (a, b) = (a + b, [a, b]) $, where $ (a, b) $ denotes the greatest common divisor (gcd) of $ a $ and $ b $, and $ [a, b] $ denotes the least common multiple (lcm) of $ a $ and $ b $.
-/
theorem number_theory_4585_1
    {a b : ℕ}
    (ha : 0 < a)
    (hb : 0 < b) :
    a.gcd b = (a + b).gcd (a.lcm b) := by

  -- Let $ d = (a, b) $. Then we can express $ a $ and $ b $ as:
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := Nat.gcd_dvd a b
  set d := a.gcd b with hd
  have hdpos : d > 0 := Nat.gcd_pos_of_pos_left b ha

  -- a + b = d \cdot m + d \cdot n = d(m + n)
  have hadd : a + b = d * (m + n) := by
    rw [hm, hn, mul_add]

  -- [a, b] = \frac{a \cdot b}{(a, b)} = \frac{(d \cdot m)(d \cdot n)}{d} = d \cdot m \cdot n
  have hlcm : a.lcm b = d * m * n := by
    rw [Nat.lcm, ← hd, hn, mul_comm d, ← mul_assoc, Nat.mul_div_cancel, hm]
    exact Nat.gcd_pos_of_pos_left b ha

  -- Since $ m $ and $ n $ are coprime, $ (m + n, m \cdot n) = 1 $
  have hmn: (m + n).gcd (m * n) = 1 := by
    have hcopr : m.Coprime n := by
      rw [← Nat.div_eq_of_eq_mul_right hdpos hm, ← Nat.div_eq_of_eq_mul_right hdpos hn]
      exact Nat.coprime_div_gcd_div_gcd hdpos
    apply Nat.Coprime.mul_right
    . refine Nat.coprime_self_add_left.mpr ?H1.a
      exact Nat.coprime_comm.mp hcopr
    . exact Nat.coprime_add_self_left.mpr hcopr

  rw [hadd, hlcm, mul_assoc, Nat.gcd_mul_left, hmn, mul_one]

/- b) Find the two positive integers whose sum is 798 and whose least common multiple is 10780. -/
theorem number_theory_4585_2
    (x y : ℕ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hsum : x + y = 798)
    (hlcm : Nat.lcm x y = 10780) :
    (x = 308 ∧ y = 490) ∨ (x = 490 ∧ y = 308) := by

  have d_eq : x.gcd y = 14 := by
    rw [number_theory_4585_1 hx hy, hsum, hlcm]
    norm_num

  set d := x.gcd y with hd
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := Nat.gcd_dvd x y
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left y hx

  have m_eq : m = x / d := (Nat.div_eq_of_eq_mul_right hdpos hm).symm
  have n_eq : n = y / d := (Nat.div_eq_of_eq_mul_right hdpos hn).symm

  have h_mnsum : m + n = (x + y) / d := by
    rw [m_eq, n_eq]
    exact (Nat.add_div_of_dvd_left (Nat.gcd_dvd_right x y)).symm

  have h_mnprod : m * n = x.lcm y / d := by
    rw [m_eq, n_eq, hd, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right x y)]
    refine Eq.symm ((fun {a b d} hda hdb => (Nat.div_left_inj hda hdb).mpr) ?hda ?hdb ?_)
    . rw [← hd, hn, ← hd, mul_comm d, ← mul_assoc, Nat.mul_div_cancel _ hdpos, hm, hd, mul_assoc]
      exact Nat.dvd_mul_right _ _
    . rw [← hd, hm, ← hd, Nat.mul_div_cancel_left _ hdpos, hn, mul_comm, mul_assoc]
      exact Nat.dvd_mul_right _ _
    . conv => lhs; rw [← hd, hn, ← hd, mul_comm d, ← mul_assoc, Nat.mul_div_cancel _ hdpos, hm]
      conv => rhs; rw [← hd, hm, ← hd, mul_comm d, Nat.mul_div_cancel _ hdpos, hn, mul_comm, mul_assoc, mul_comm n, ← mul_assoc]

  -- m * n = 770, m + n = 57
  simp [hsum, d_eq] at h_mnsum
  simp [hlcm, d_eq] at h_mnprod

  have l_sub_pow2 (a b : ℕ) : b ≤ a → (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by
    intro h
    symm
    calc (a + b) ^ 2 - 4 * (a * b)
      _ = a * a + b * b + 2 * (a * b) - (2 + 2) * (a * b):= by
        ring_nf
      _ = a * a + b * b - 2 * (a * b) := by
        omega
      _ = (a - b) ^ 2 := by
      --_ = a * a + a * b - a * b + b * b - 2 * (a * b) := by
        rw [← Nat.add_sub_cancel (a * a) (a * b)]
      --_ = a * a + a * b - (a - b) * b - 2 * (a * b) := by
        rw [← Nat.sub_add_comm (show a * b ≤ a * a + (a * b) by omega)]
        rw [Nat.Simproc.add_sub_le _ (Nat.mul_le_mul_right b h)]
        rw [← Nat.sub_mul a b b]
      --_ = (a - b) * a - (a - b) * b := by
        rw [← Nat.sub_add_cancel (Nat.mul_le_mul_right a h)]
        rw [← Nat.sub_mul a b a, mul_comm b a]
        rw [add_assoc, ← two_mul (a * b)]
        rw [Nat.sub_add_comm (Nat.mul_le_mul_left (a - b) h)]
        rw [Nat.add_sub_self_right ((a - b) * a - (a - b) * b) (2 * (a * b))]
      --_ = (a - b) ^ 2 := by
        rw [← Nat.mul_sub_left_distrib (a - b) a b]
        rw [← Nat.pow_two (a - b)]


  -- solve the two equation and get answer (the solution didn't give the detailed steps)
  have : n ≤ m ∧ m - n = 13 ∨ m ≤ n ∧ n - m = 13 := by
    by_cases h : n ≤ m
    . left; show n ≤ m ∧ m - n = 13
      have t1 := l_sub_pow2 m n h
      simp [h_mnsum, h_mnprod] at t1
      have t2 : m - n  = Nat.sqrt 169 := by rw [← t1, Nat.sqrt_eq']
      rw [Nat.sqrt_eq' 13] at t2
      exact ⟨h, t2⟩
    . right; show m ≤ n ∧ n - m = 13
      apply Nat.le_of_not_ge at h
      have t1 := l_sub_pow2 n m h
      rw [add_comm] at h_mnsum
      rw [mul_comm] at h_mnprod
      simp [h_mnsum, h_mnprod] at t1
      have t2 : n - m  = Nat.sqrt 169 := by rw [← t1, Nat.sqrt_eq']
      rw [Nat.sqrt_eq' 13] at t2
      exact ⟨h, t2⟩

  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  . simp [show n = 22 by omega, ← hd, d_eq] at hn
    simp [show m = 35 by omega, ← hd, d_eq] at hm
    right; exact ⟨hm, hn⟩
  . simp [show n = 35 by omega, ← hd, d_eq] at hn
    simp [show m = 22 by omega, ← hd, d_eq] at hm
    left; exact ⟨hm, hn⟩
