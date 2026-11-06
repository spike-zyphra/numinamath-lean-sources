import Mathlib

/- The square of 9 is divided by the cube root of 125. What is the remainder?
(A) 6
(B) 3
(C) 16
(D) 2
(E) 1-/
theorem arithmetic_4186 {n m : ℕ} (hn : n ^ 3 = 125) (hm : m = 9 ^ 2): m % n = 1 := by
  -- **Compute the cube root of 125:**
  --  \[
  --  \sqrt[3]{125} = 5
  --  \]
  --  This is because:
  --  \[
  --  5^3 = 125
  --  \]
  rw [show 125 = 5 ^ 3 by ring] at hn
  have : n = 5 := by
    apply Nat.pow_left_injective <| show 3 ≠ 0 by norm_num
    simpa
  rw [this, hm]
  -- **Divide 81 by 5 and find the remainder:**
  --  - First, calculate the quotient:
  --    \[
  --    \frac{81}{5} = 16 \quad \text{with a remainder}
  --    \]
  --    Since \( 81 \div 5 \) gives 16 as the quotient.

  --  - To find the remainder \( r \), use the equation for division:
  --    \[
  --    81 = 5 \times 16 + r
  --    \]
  --    Solve for \( r \):
  --    \[
  --    r = 81 - 5 \times 16
  --    \]
  --    \[
  --    r = 81 - 80
  --    \]
  --    \[
  --    r = 1
  --    \]
  norm_num
