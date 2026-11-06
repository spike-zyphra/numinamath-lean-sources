import Mathlib

/- Show that the integer \( n \) is even if and only if \( n - 2\left\lfloor \frac{n}{2} \right\rfloor = 0 \).-/
theorem number_theory_4890 (n : ℤ) : Even n ↔ n - 2 * ⌊n / 2⌋ = 0 := by
  constructor
  --  1. **If \( n \) is even, then \( n - 2\left\lfloor \frac{n}{2} \right\rfloor = 0 \)**:
  --  - An integer \( n \) is even if it can be expressed as \( n = 2k \) for some integer \( k \).
  --  - When we divide \( n \) by 2, we have \( \frac{n}{2} = k \).
  --  - The floor function \( \left\lfloor \frac{n}{2} \right\rfloor \) will also equal \( k \) since \( k \) is an integer.
  --  - Therefore, \( 2\left\lfloor \frac{n}{2} \right\rfloor = 2k = n \).
  --  - Substituting this back into the expression gives us:
  --    \[
  --    n - 2\left\lfloor \frac{n}{2} \right\rfloor = n - n = 0.
  --    \]
  --  - Thus, if \( n \) is even, then \( n - 2\left\lfloor \frac{n}{2} \right\rfloor = 0 \).
  . rintro ⟨k, rfl⟩
    simp [← two_mul]
  --  2. **If \( n - 2\left\lfloor \frac{n}{2} \right\rfloor = 0 \), then \( n \) is even**:
  --  - Assume \( n - 2\left\lfloor \frac{n}{2} \right\rfloor = 0 \).
  --  - This implies that \( n = 2\left\lfloor \frac{n}{2} \right\rfloor \).
  --  - Let \( k = \left\lfloor \frac{n}{2} \right\rfloor \). Then we can write \( n = 2k \).
  --  - Since \( k \) is an integer, \( n \) can be expressed as \( n = 2k \), which means \( n \) is even.
  . intro h
    use ⌊n/2⌋
    linear_combination h
