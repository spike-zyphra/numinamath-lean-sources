import Mathlib

/- To prove this statement, we start by recalling the definition of a pseudoprime.
A composite number \( n \) is called a pseudoprime to a base \( a \) if it satisfies the congruence \( a^{n-1} \equiv 1 \mod n \). -/
def isPseudoprime (n : ℤ) (b : ℤ) : Prop := b^n.natAbs ≡ b [ZMOD n]

/- Show that if \( n \) is a pseudoprime to the bases \( a \) and \( b \), then \( n \) is also a pseudoprime to the base \( ab \).-/
theorem number_theory_4827
    (n a b : ℤ) (nah : isPseudoprime n a) (nbh : isPseudoprime n b)
    : isPseudoprime n (a*b) := by

-- Given that \( n \) is a pseudoprime to the bases \( a \) and \( b \), we have:
-- 1. \( a^{n-1} \equiv 1 \mod n \)
-- 2. \( b^{n-1} \equiv 1 \mod n \)

  simp [isPseudoprime] at nah nbh ⊢

-- We want to show that \( n \) is also a pseudoprime to the base \( ab \), which means we need to demonstrate that:
-- \[
-- (ab)^{n-1} \equiv 1 \mod n
-- \]

-- Using the property of modular arithmetic, we can express \( (ab)^{n-1} \) as:
-- \[
-- (ab)^{n-1} = a^{n-1} b^{n-1}
-- \]

-- Now, we can substitute the congruences we have for \( a^{n-1} \) and \( b^{n-1} \):
-- \[
-- (ab)^{n-1} \equiv a^{n-1} b^{n-1} \mod n
-- \]

  rw [mul_pow]

-- From our assumptions, we know:
-- \[
-- a^{n-1} \equiv 1 \mod n \quad \text{and} \quad b^{n-1} \equiv 1 \mod n
-- \]

-- Thus, we can substitute these results into our expression:
-- \[
-- (ab)^{n-1} \equiv 1 \cdot 1 \mod n
-- \]

-- This simplifies to:
-- \[
-- (ab)^{n-1} \equiv 1 \mod n
-- \]

  apply Int.ModEq.mul nah nbh

-- Since we have shown that \( (ab)^{n-1} \equiv 1 \mod n \), we conclude that \( n \) is indeed a pseudoprime to the base \( ab \).

-- Therefore, we have proven that if \( n \) is a pseudoprime to the bases \( a \) and \( b \), then \( n \) is also a pseudoprime to the base \( ab \).
