import Mathlib

/- For what value of x does 10^x * 100^(2x) = 1000^5 ?
(A) 1
(B) 2
(C) 3
(D) 4
(E) 5 -/

theorem algebra_95692 (x : ℕ) (hx : 10^x * 100^(2 * x) = 1000^5) : x = 3 := by
  -- bring everything as power of 10 to get 10^(5x) = 10^15
  have hx' : 10^(5 * x) = 10 ^ 15 := by
    calc
      10 ^ (5 * x) = 10 ^ ( x + (4 * x)) := by ring
      _ = 10 ^ x * 10 ^ (2 * (2 * x)) := by ring
      _ = 10 ^ x * (10 ^ 2) ^ (2 * x) := by rw [Nat.pow_mul]
      _ = 10 ^ x * 100 ^ (2 * x) := by norm_num
      _ = 1000^5 := by rw [hx]
      _ = 10^15 := by norm_num
  -- since 10 > 1, 10^(5x) = 10^15 implies 5x = 15
  have hx'': 5 * x = 15 := by
    exact (pow_right_inj₀ (by norm_num: 0 < 10) (by norm_num: 10 ≠ 1)).mp hx'
  -- linarith easily proves x = 3
  linarith