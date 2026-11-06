import Mathlib
/- Let $B$ be an integer such that $B$ is a multiple of $4$ and $B^2 \equiv -1 \pmod{25}$. Let $E$ be a positive integer that is a multiple of $4$. Show that the last two digits of $B^E$ are $76$. -/
theorem number_theory_636697 (B : ℤ) (E : ℕ) (hpos : E > 0) (hB1 : B ^ 2 ≡ -1 [ZMOD 25]) (hB2 : 4 ∣ B) (hE : 4 ∣ E) : B ^ E ≡ 76 [ZMOD 100]:= by
  -- Extract k from the divisibility condition 4|E, where E = 4k
  rcases hE with ⟨k, hk⟩
  subst E
  -- Prove that (B^2)^(2k) ≡ (-1)^(2k) (mod 25) using the given condition
  have hb : (B ^ 2) ^ (2 * k) ≡ (-1) ^ (2 * k) [ZMOD 25]:= by exact Int.ModEq.pow (2 * k) hB1
  simp at hb
  ring_nf at hb
  -- Rewrite 4k as k*4 using omega tactic
  rw [show 4 * k = k * 4 by omega]
  -- Use the condition 4|B to show B ≡ 0 (mod 4)
  replace hB2 : B ≡ 0 [ZMOD 4]:= by exact Dvd.dvd.modEq_zero_int hB2
  -- Show that B^(k*4) ≡ 0^(k*4) (mod 4)
  replace hB2 : B ^ (k * 4) ≡ 0 ^ (k * 4) [ZMOD 4]:= by exact Int.ModEq.pow (k * 4) hB2
  -- Simplify 0^(k*4) to 0
  rw [show (0 : ℤ) ^ (k * 4) = 0 by refine zero_pow (by omega)] at hB2
  -- Show B^(k*4) ≡ 76 (mod 25)
  replace hb : B ^ (k * 4) ≡ 76 [ZMOD 25]:= by exact hb
  -- Show B^(k*4) ≡ 76 (mod 4)
  replace hB2 : B ^ (k * 4) ≡ 76 [ZMOD 4]:= by exact hB2
  -- Rewrite 100 as 25*4
  rw [show (100 : ℤ) = 25 * 4 by omega]
  -- Prove that 25 and 4 are coprime
  have g1 : IsCoprime (25 : ℤ) 4:= by norm_num
  -- Use Chinese Remainder Theorem to combine the congruences
  suffices 25 * 4 ∣ B ^ (k * 4) - 76 by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) this)
  -- Show that 25 divides B^(k*4) - 76
  replace hb : 25 ∣ B ^ (k * 4) - 76:= by exact Int.ModEq.dvd (id (Int.ModEq.symm hb))
  -- Show that 4 divides B^(k*4) - 76
  replace hB2 : 4 ∣ B ^ (k * 4) - 76:= by exact Int.ModEq.dvd (id (Int.ModEq.symm hB2))
  -- Complete the proof using coprimality of 25 and 4
  exact IsCoprime.mul_dvd g1 hb hB2
