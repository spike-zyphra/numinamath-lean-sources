import Mathlib

/- What number should be placed in the box to make \( 10^{4} \times 100^{\square}=1000^{6} \) ?
(A) 7
(B) 5
(C) 2
(D) \(\frac{3}{2}\)
(E) 10-/
theorem algebra_4018 {n : ℕ} : 10 ^ 4 * 100 ^ n = 1000 ^ 6 ↔ n = 7 := by
  constructor
  . intro h
    conv at h =>
  --    \[
  --  10^4 \times (10^2)^{\square} = (10^3)^6
  --  \]
      rw [show 100 = 10 ^ 2 by decide, show 1000 = 10 ^ 3 by decide]
    --    \[
    --  10^4 \times 10^{2 \times \square} = 10^{3 \times 6}
    --  \]
      rw [← pow_mul, ← pow_add, ← pow_mul]
  --   **Set the exponents equal to each other:**
  --  \[
  --  4 + 2\square = 18
  --  \]
    replace h := Nat.pow_right_injective (by decide) h
  --   \[
  --  \square = 7
  --  \]
    linarith
  -- verify n=7 is correct answer
  intro h
  rw [h]
  norm_num
