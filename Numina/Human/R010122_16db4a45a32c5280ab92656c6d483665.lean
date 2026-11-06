import Mathlib

/- Find the product of $10101_2$ and $101_2$. Express your answer in base $2$. -/
theorem number_theory_14406 : (0b10101 : ℕ) * 0b101 = 0b1101001 := by
  -- we can do the calculation with base 10.
  have h1: 0b10101 = 21 := calc
    0b10101 = 1 + 1*2^2 + 1*2^4 := by ring
    _ = 1 + 4 + 16 := by ring
    _ = 21 := by ring
  have h2: 0b101 = 5 := calc
    0b101 = 1 + 1*2^2 := by ring
    _ = 5 := by ring
  -- so 0b10101 x 0b101 = 21 x 5 = 101
  have h3: 0b10101 * 0b101 = 105 := by
    rw [h1,h2]
  -- and we should express 101 with base 2.
  have h4: 105 = 0b1101001 := calc
    105 = 64 + 32 + 9 := by ring
    _ = 64 + 32 + 8 + 1 := by ring
    -- notice that 2^2=4, 4^2=16=2^4. so 32 = 2^5 and 64=2^6
    _ = 1*2^6 + 1*2^5 + 1*2^3 + 1*2^0 := by ring
    _ = 0b1101001 := by ring
  rw [← h4, h3]