import Mathlib

/- To prove this statement, we start by recalling the definition of a pseudoprime.
A composite number \( n \) is called a pseudoprime to a base \( a \) if it satisfies the congruence \( a^{n-1} \equiv 1 \mod n \). -/
def isPseudoprime (n : ℤ) (b : ℤ) : Prop := b^n.natAbs ≡ b [ZMOD n]

theorem number_theory_4827
    (n a b : ℤ) (nah : isPseudoprime n a) (nbh : isPseudoprime n b)
    : isPseudoprime n (a*b) := by 
  unfold isPseudoprime at nah nbh ⊢
  have h1 : (a * b) ^ n.natAbs = (a ^ n.natAbs) * (b ^ n.natAbs) := by
    rw [mul_pow]
  rw [h1]
  exact Int.ModEq.mul nah nbh