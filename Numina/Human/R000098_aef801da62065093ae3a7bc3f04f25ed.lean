import Mathlib

/- determine -/ abbrev gcd_a : ℕ := (2^2) * (3^3) * (5^3) * (7^2)
/- determine -/ abbrev lcm_a : ℕ := (2^7) * (3^5) * (5^5) * (7^7)
/- determine -/ abbrev gcd_b : ℤ := 1
/- determine -/ abbrev lcm_b : ℤ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29
/- determine -/ abbrev gcd_c : ℤ := 2 * 5 * 11
/- determine -/ abbrev lcm_c : ℤ := (2^3) * (5^7) * (11^13) * 3 * 7 * 13
/- determine -/ abbrev gcd_d : ℤ := 101^1000
/- determine -/ abbrev lcm_d : ℤ := (41^11) * (47^11) * (79^111) * (83^111) * (101^1001)

/- Find the greatest common divisor (GCD) and least common multiple (LCM) of the following pairs of integers:
a) $2^{2} 3^{3} 5^{5} 7^{7}$ and $2^{7} 3^{5} 5^{3} 7^{2}$ -/
theorem number_theory_4578_1
    (n1 n2 : ℕ)
    (h₀ : n1 = (2^2) * (3^3) * (5^5) * (7^7))
    (h₁ : n2 = (2^7) * (3^5) * (5^3) * (7^2))
    : (n1.gcd n2 = gcd_a) ∧ (lcm n1 n2 = lcm_a) := by
  rw [h₀, h₁, gcd_a, lcm_a]
  native_decide

/- Find the greatest common divisor (GCD) and least common multiple (LCM) of the following pairs of integers:
b) $2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ and $17 \cdot 19 \cdot 23 \cdot 29$ -/
theorem number_theory_4578_2
    (n1 n2 : ℤ)
    (h₀ : n1 = 2 * 3 * 5 * 7 * 11 * 13)
    (h₁ : n2 = 17 * 19 * 23 * 29)
    : (n1.gcd n2 = gcd_b) ∧ (lcm n1 n2 = lcm_b) := by
  rw [h₀, h₁, gcd_b, lcm_b]
  native_decide

/- Find the greatest common divisor (GCD) and least common multiple (LCM) of the following pairs of integers:
c) $2^{3} 5^{7} 11^{13}$ and $2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ -/
theorem number_theory_4578_3
    (n1 n2 : ℤ)
    (h₀ : n1 = (2^3) * (5^7) * (11^13))
    (h₁ : n2 = 2 * 3 * 5 * 7 * 11 * 13)
    : (n1.gcd n2 = gcd_c) ∧ (lcm n1 n2 = lcm_c) := by
  rw [h₀, h₁, gcd_c, lcm_c]
  native_decide

/- Find the greatest common divisor (GCD) and least common multiple (LCM) of the following pairs of integers:
d) $47^{11} 79^{111} 101^{1001}$ and $41^{11} 83^{111} 101^{1000}$ -/
theorem number_theory_4578_4
    (n1 n2 : ℤ)
    (h₀ : n1 = (47^11) * (79^111) * (101^1001))
    (h₁ : n2 = (41^11) * (83^111) * (101^1000))
    : (n1.gcd n2 = gcd_d) ∧ (lcm n1 n2 = lcm_d) := by
  rw [h₀, h₁, gcd_d, lcm_d]
  native_decide
