import Mathlib

/- To demonstrate that every odd composite integer is a pseudoprime to both bases,
we will first define what a pseudoprime is. An integer \( n \) is called a pseudoprime
to a base \( a \) if \( a^{n-1} \equiv 1 \mod n \) holds true, even though \( n \) is not a prime number.-/
def isPseudoprime1 (n : ℤ) (b : ℤ) : Prop := b^n.natAbs ≡ b [ZMOD n]

/- Show that every odd composite integer is a pseudoprime to both the base 1 and the base -1.-/
theorem number_theory_4821
    (n : ℤ) (n_odd : Odd n) (n_comp : ∃ m : ℕ, ∃ p : Fin m → ℤ, ∏ i, p i = n)
    : isPseudoprime1 n 1 ∧ isPseudoprime1 n (-1) := by
-- 1. **Base 1**: For any integer \( n \), we have \( 1^{n-1} = 1 \). Therefore, \( 1^{n-1} \equiv 1 \mod n \) holds true for any integer \( n \), including odd composite integers. Thus, every odd composite integer is a pseudoprime to the base 1.

-- 2. **Base -1**: For any odd integer \( n \), we have \( (-1)^{n-1} = 1 \). Therefore, \( (-1)^{n-1} \equiv 1 \mod n \) holds true for any integer \( n \), including odd composite integers. Thus, every odd composite integer is a pseudoprime to the base -1.

-- 3. **Conclusion**: Since both conditions \( 1^{n-1} \equiv 1 \mod n \) and \( (-1)^{n-1} \equiv 1 \mod n \) are satisfied for every odd composite integer \( n \), we conclude that every odd composite integer is indeed a pseudoprime to both the base 1 and the base -1.

  simp [isPseudoprime1, Odd.neg_one_pow (Odd.natAbs n_odd)]
