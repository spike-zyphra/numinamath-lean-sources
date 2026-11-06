import Mathlib

/- If $2004$ is split after the third digit into a three-digit integer  and a one-digit integer, then the two integers, $200$ and $4$, have  a common factor greater than one.  The years $2005$ and $2006$  each have this same property, too.  What is the first    odd-numbered year after $2006$ that has this property? -/
theorem algebra_21182 : IsLeast {n : ℕ | n > 2006 ∧ gcd (n / 10) (n % 10) > 1 ∧ Odd n} 2013 := by
  -- We need to show that 2013 is the smallest number in the set
  -- By first showing that 2013 is in the set
  -- Then showing that any number smaller than 2013 is not in the set
  constructor
  . -- Simplifying is enough to show that 2013 is in the set
    simp
    trivial
  . -- We need to show that any number smaller than 2013 is not in the set
    rintro n ⟨h1, h2, h3⟩
    by_contra! H
    -- Enumerate all the 6 cases
    interval_cases n
    -- They are all impossible
    all_goals
      trivial
