import Mathlib
/- 15th Eötvös 1908 Problem 1 m and n are odd. Show that 2 k divides m 3 - n 3 iff it divides m - n. -/
theorem number_theory_143178 (k : ℕ) (m n : ℤ) (hm : Odd m) (hn : Odd n) : 2 ^ k ∣ m ^ 3 - n ^ 3 ↔ 2 ^ k ∣ m - n:= by
  constructor
  -- First direction: proving that if 2^k divides m^3 - n^3, then 2^k divides m - n
  .
    intro h
    -- Factor m^3 - n^3 as (m - n) * (m^2 + m*n + n^2)
    rw [show m ^ 3 - n ^ 3 = (m - n) * (m ^ 2 + m * n + n ^ 2) by ring_nf] at h
    -- Prove that m^2 is odd
    have g1 : Odd (m ^ 2):= by exact Odd.pow hm
    -- Prove that m*n is odd
    have g2 : Odd (m * n):= by exact Odd.mul hm hn
    -- Prove that n^2 is odd
    have g3 : Odd (n ^ 2):= by exact Odd.pow hn
    -- Prove that m^2 + m*n is even (sum of two odd numbers)
    have g4 : Even (m ^ 2 + m * n):= by exact Odd.add_odd g1 g2
    -- Prove that m^2 + m*n + n^2 is odd (even + odd = odd)
    have g5 : Odd (m ^ 2 + m * n + n ^ 2):= by exact Even.add_odd g4 g3
    -- Prove that 2 and m^2 + m*n + n^2 are coprime
    have g6 : IsCoprime 2 (m ^ 2 + m * n + n ^ 2):= by
      simp [Odd] at g5
      rcases g5 with ⟨k, hk⟩
      rw [hk]
      simp [IsCoprime]
      use -k, 1
      linarith
    -- Extend coprimality to 2^k and m^2 + m*n + n^2
    replace g6 : IsCoprime (2 ^ k) (m ^ 2 + m * n + n ^ 2):= by exact IsCoprime.pow_left g6
    -- If 2^k divides a product where one factor is coprime to 2^k, then 2^k divides the other factor
    exact IsCoprime.dvd_of_dvd_mul_right g6 h
  -- Second direction: proving that if 2^k divides m - n, then 2^k divides m^3 - n^3
  .
    intro h
    -- Factor m^3 - n^3 as (m - n) * (m^2 + m*n + n^2)
    rw [show m ^ 3 - n ^ 3 = (m - n) * (m ^ 2 + m * n + n ^ 2) by ring_nf]
    -- If 2^k divides m - n, then it divides (m - n) * (m^2 + m*n + n^2)
    exact Dvd.dvd.mul_right h (m ^ 2 + m * n + n ^ 2)
