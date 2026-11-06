import Mathlib
/- Soient $a, b$ deux entiers. Montrer que $a b(a-b)$ est divisible par 2. -/
theorem number_theory_607424 (a b : ℤ) : 2 ∣ a * b * (a - b):= by
  -- Case analysis: either a is even or b is even
  by_cases h : Even a ∨ Even b
  .
    -- Split the disjunction into two cases
    rcases h with h | h
    .
      -- Case 1: a is even
      -- Replace the hypothesis with "2 divides a"
      replace h : 2 ∣ a:= by exact even_iff_two_dvd.mp h
      -- Rearrange the expression to factor out a
      rw [show a * b * (a - b) = a * (b * (a - b)) by ring]
      -- Since 2 divides a, it also divides a multiplied by any expression
      exact Dvd.dvd.mul_right h (b * (a - b))
    .
      -- Case 2: b is even
      -- Replace the hypothesis with "2 divides b"
      replace h : 2 ∣ b:= by exact even_iff_two_dvd.mp h
      -- Rearrange the expression to factor out b
      rw [show a * b * (a - b) = b * (a * (a - b)) by ring]
      -- Since 2 divides b, it also divides b multiplied by any expression
      exact Dvd.dvd.mul_right h (a * (a - b))
  .
    -- Case 3: Neither a nor b is even (both are odd)
    -- Simplify the negation of the disjunction
    simp at h
    -- Extract the two facts: a is odd and b is odd
    rcases h with ⟨h1, h2⟩
    -- If a and b are both odd, then their difference is even
    replace h1 : Even (a - b):= by exact Odd.sub_odd h1 h2
    -- Replace with "2 divides (a-b)"
    replace h1 : 2 ∣ a - b:= by exact even_iff_two_dvd.mp h1
    -- Since 2 divides (a-b), it also divides (a-b) multiplied by any expression
    exact Dvd.dvd.mul_left h1 (a * b)
