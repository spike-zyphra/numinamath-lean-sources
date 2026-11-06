import Mathlib

/- We can verify a multiplication \( c = a b \) by checking whether the congruence \( c \equiv a b \pmod{m} \) holds true, where \( m \) is any modulus. If we find that \( c \neq a b \pmod{m} \), then we know an error has occurred. When we set \( m = 9 \) and use the fact that an integer in decimal notation is congruent modulo 9 to the sum of its digits, this method is known as casting out nines. We need to check each of the following multiplications using casting out nines:
a) \( 875961 \cdot 2753 = 2410520633 \)
b) \( 14789 \cdot 23567 = 348532367 \)
c) \( 24789 \cdot 43717 = 1092700713 \)
d) Are your checks foolproof?-/
theorem number_theory_4756 : ¬(875961 * 2753 ≡ 2410520633[ZMOD 9]) ∧
    ¬(14789 * 23567 ≡ 348532367[ZMOD 9]) ∧
    (24789 * 43717 ≡ 1092700713[ZMOD 9]) := by
  -- verify by computation
  native_decide
