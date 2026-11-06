import Mathlib

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

theorem number_theory_4585_2
    (x y : ℕ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hsum : x + y = 798)
    (hlcm : Nat.lcm x y = 10780) :
    (x = 308 ∧ y = 490) ∨ (x = 490 ∧ y = 308) := by

  have h1 : y = 798 - x := by 
    omega

  rw [h1] at hlcm

  have h2 : x ≤ 798 := by 
    omega

  interval_cases x <;> norm_num [Nat.lcm] at hlcm
  <;> omega