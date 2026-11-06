import Mathlib

/-What is the remainder when $2^3 \cdot 4^5 \cdot 6^7 \cdot 8^9$ is divided by 13?-/
theorem number_theory_23080 : (2^3 * 4^5 * 6^7 * 8^9) % (13 : ℤ) = 8 := by
  -- The prime factorization of $2^3 \cdot 4^5 \cdot 6^7 \cdot 8^9$ is $2^{47} \cdot 3^7$.
  have h1 : (2 : ℤ)^3 * 4^5 * 6^7 * 8^9 = 2^47 * 3^7 := by
    linarith
  rw [h1]
  change _ ≡ 8 [ZMOD 13]
  -- We see that $2^6 \equiv 64 \equiv -1 \pmod{13}$, so \[2^{47} \equiv 2^{6 \cdot 7 + 5} \equiv (2^6)^7 \cdot 2^5 \equiv (-1)^7 \cdot 32 \equiv -32 \equiv 7 \pmod{13},\].
  have h2 : 2^6 ≡ -1 [ZMOD 13] := rfl
  have h3 : 2^47 ≡ 7 [ZMOD 13] := by
    rw [show 47 = 6 * 7 + 5 by omega, pow_add, pow_mul]
    change _ ≡ (-1)^7 * 32 [ZMOD 13]
    refine Int.ModEq.mul (Int.ModEq.pow 7 h2) rfl
  -- $3^7 \equiv 2187 \equiv 3 \pmod{13}$, so $2^{47} \cdot 3^7 \equiv 7 \cdot 3 \equiv 21 \equiv \boxed{8} \pmod{13}$.
  change _ ≡ 7 * 3 [ZMOD 13]
  exact Int.ModEq.mul h3 rfl
