import Mathlib
/- Let $p$ be a prime number. Let $b$ be an integer such that $1 \le b < p$. Suppose $c$ is the modular inverse of $b$ modulo $p$ (meaning $bc \equiv 1 \pmod p$ and $1 \le c < p$). Determine the modular inverse of the integer $p-c$ modulo $p$. Show that this inverse is $p-b$. Express your answer as an integer from $0$ to $p-1$, inclusive. -/
theorem algebra_640208 (b c p : ℕ) (hb1 : 1 ≤ b) (hb2 : b ≤ p) (hc1 : 1 ≤ c) (hc2 : c ≤ p) (hp : Nat.Prime p) (hbc : b * c ≡ 1 [MOD p]) : 1 ≤ p - b ∧ p - b ≤ p ∧ (p - c) * (p - b) ≡ 1 [MOD p]:= by
  -- Split the conjunction into three parts
  refine ⟨?_, by omega, ?_⟩
  -- First part: prove 1 ≤ p - b by contradiction
  by_contra H
  -- Assume the negation: p - b < 1, which means b ≥ p
  replace H : b = p:= by omega
  -- Substitute b = p into the original equation
  subst b
  -- Now we have p * c ≡ 1 (mod p), but p * c ≡ 0 (mod p)
  have h3 : p * c ≡ 0 [MOD p]:= by
    -- p divides p * c trivially
    suffices p ∣ p * c by exact Nat.modEq_zero_iff_dvd.mpr this
    simp
  -- This gives us 1 ≡ 0 (mod p) by transitivity
  replace hbc : 1 ≡ 0 [MOD p]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h3)) hbc)
  -- Which means p divides 1
  replace hbc : p ∣ 1:= by exact Nat.dvd_of_mod_eq_zero hbc
  -- But this is impossible since p > 1 for any prime p
  simp at hbc
  have hpge : p > 1:= by exact Nat.Prime.one_lt hp
  linarith
  -- Third part: prove (p - c) * (p - b) ≡ 1 (mod p)
  -- Use the strategy: add p*(b+c) to both sides and show equivalence
  suffices (p - c) * (p - b) + p * (b + c) ≡ 1 + p * (b + c) [MOD p] by exact Nat.ModEq.add_right_cancel' (p * (b + c)) this
  -- Expand the left side algebraically
  have g1 : (p - c) * (p - b) + p * (b + c) = b * c + p ^ 2:= by
    rify
    field_simp
    ring_nf
  rw [g1]
  -- Show that p^2 ≡ p*(b+c) (mod p) since both are ≡ 0 (mod p)
  have g2 : p ^ 2 ≡ p * (b + c) [MOD p]:= by
    -- p^2 ≡ 0 (mod p)
    have g3 : p ^ 2 ≡ 0 [MOD p]:= by
      suffices p ∣ p ^ 2 by exact Nat.modEq_zero_iff_dvd.mpr this
      use p
      ring
    -- p*(b+c) ≡ 0 (mod p)
    have g4 : p * (b + c) ≡ 0 [MOD p]:= by
      suffices p ∣ p * (b + c) by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    -- Therefore p^2 ≡ p*(b+c) (mod p)
    exact Nat.ModEq.trans g3 (id (Nat.ModEq.symm g4))
  -- Combine: b*c + p^2 ≡ 1 + p*(b+c) (mod p)
  exact Nat.ModEq.add hbc g2
