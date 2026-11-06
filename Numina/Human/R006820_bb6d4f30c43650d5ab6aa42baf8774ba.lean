import Mathlib
/- Let $a$ be an integer. Consider the system of congruences:
$$
\left\{\begin{array}{l}
x \equiv a \pmod 3 \\
x \equiv -1 \pmod 5 \\
x \equiv 2 \pmod 7 \\
x \equiv -2 \pmod {11}
\end{array}\right.
$$
Show that $x \equiv 385a + 9 \pmod{1155}$. -/
theorem number_theory_641444 (a x : ℤ) (h1 : x ≡ a [ZMOD 3]) (h2 : x ≡ -1 [ZMOD 5]) (h3 : x ≡ 2 [ZMOD 7]) (h4 : x ≡ -2 [ZMOD 11]) : x ≡ 385 * a + 9 [ZMOD 1155]:= by

  -- First, prove that x ≡ 385a + 9 (mod 3)
  -- We show that a ≡ 385a + 9 (mod 3) by proving 3 divides 385a + 9 - a
  replace h1 : x ≡ 385 * a + 9 [ZMOD 3]:= by
    suffices a ≡ 385 * a + 9 [ZMOD 3] by exact Int.ModEq.trans h1 this
    suffices 3 ∣ 385 * a + 9 - a by exact Int.modEq_iff_dvd.mpr this
    use 128 * a + 3
    ring

  -- Next, prove that x ≡ 385a + 9 (mod 5)
  -- We show that -1 ≡ 385a + 9 (mod 5) by proving 5 divides 385a + 9 + 1
  replace h2 : x ≡ 385 * a + 9 [ZMOD 5]:= by
    suffices -1 ≡ 385 * a + 9 [ZMOD 5] by exact Int.ModEq.trans h2 this
    suffices 5 ∣ 385 * a + 9 + 1 by exact Int.modEq_iff_dvd.mpr this
    use 77 * a + 2
    ring

  -- Then, prove that x ≡ 385a + 9 (mod 7)
  -- We show that 2 ≡ 385a + 9 (mod 7) by proving 7 divides 385a + 9 - 2
  replace h3 : x ≡ 385 * a + 9 [ZMOD 7]:= by
    suffices 2 ≡ 385 * a + 9 [ZMOD 7] by exact Int.ModEq.trans h3 this
    suffices 7 ∣ 385 * a + 9 - 2 by exact Int.modEq_iff_dvd.mpr this
    use 55 * a + 1
    ring

  -- Finally, prove that x ≡ 385a + 9 (mod 11)
  -- We show that -2 ≡ 385a + 9 (mod 11) by proving 11 divides 385a + 9 + 2
  replace h4 : x ≡ 385 * a + 9 [ZMOD 11]:= by
    suffices -2 ≡ 385 * a + 9 [ZMOD 11] by exact Int.ModEq.trans h4 this
    suffices 11 ∣ 385 * a + 9 + 2 by exact Int.modEq_iff_dvd.mpr this
    use 35 * a + 1
    ring

  -- Convert congruences to divisibility statements
  replace h1 : 3 ∣ 385 * a + 9 - x:= by exact Int.ModEq.dvd h1
  replace h2 : 5 ∣ 385 * a + 9 - x:= by exact Int.ModEq.dvd h2
  replace h3 : 7 ∣ 385 * a + 9 - x:= by exact Int.ModEq.dvd h3
  replace h4 : 11 ∣ 385 * a + 9 - x:= by exact Int.ModEq.dvd h4

  -- Prove that 3 and 5 are coprime
  have g1 : IsCoprime (3 : ℤ) 5:= by norm_num
  -- Therefore 15 divides 385a + 9 - x
  replace h1 : 3 * 5 ∣ 385 * a + 9 - x:= by exact IsCoprime.mul_dvd g1 h1 h2

  -- Prove that 7 and 11 are coprime
  have g2 : IsCoprime (7 : ℤ) 11:= by norm_num
  -- Therefore 77 divides 385a + 9 - x
  replace h3 : 7 * 11 ∣ 385 * a + 9 - x:= by exact IsCoprime.mul_dvd g2 h3 h4

  -- Prove that 15 and 77 are coprime
  have g3 : IsCoprime ((3 : ℤ) * 5) (7 * 11):= by norm_num
  -- Therefore 1155 (= 15 * 77) divides 385a + 9 - x
  replace h1:= IsCoprime.mul_dvd g3 h1 h3
  simp at h1
  -- Convert back to congruence to complete the proof
  exact Int.modEq_iff_dvd.mpr h1
