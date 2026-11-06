import Mathlib
/- Let $p$ be a prime number. Let $a$ be an integer such that $1 < a < p$. Let $b_0$ be an integer not divisible by $p$.
Let $k_0$ be the integer such that $a \cdot b_640734 \equiv k_640734 \pmod p$ and $1 \le k_640734 < p$. (Assume $a \cdot b_0$ is not a multiple of $p$).
Let $k_{0,inv}$ be the modular multiplicative inverse of $k_0$ modulo $p$.
Show that the modular multiplicative inverse of $a$ modulo $p$ is congruent to $(b_640734 \cdot k_{0,inv}) \pmod p$. -/
theorem number_theory_640734 (a b c d p k : ℕ) (hp : Nat.Prime p) (ha1 : 1 < a) (ha2 : a < p) (hk1 : 1 ≤ k) (hk2 : k < p) (h : a * b ≡ k [MOD p]) (hc : k * c ≡ 1 [MOD p]) (hd : a * d ≡ 1 [MOD p]): d ≡ (b * c) [MOD p] := by

  -- Multiply both sides of congruence (a * b ≡ k) by c
  replace h : a * b * c ≡ k * c [MOD p]:= by exact Nat.ModEq.mul h rfl

  -- Use transitivity with k * c ≡ 1 to get a * b * c ≡ 1
  replace h:= Nat.ModEq.trans h hc

  -- Multiply both sides by d
  replace h : d * (a * b * c) ≡ d * 1 [MOD p]:= by exact Nat.ModEq.mul rfl h

  -- Rearrange the left side using ring arithmetic
  rw [show d * (a * b * c) = b * c  * (a * d) by ring] at h

  -- Simplify the right side
  simp at h

  -- Apply the fact that a * d ≡ 1 to get the final congruence
  replace hd : b * c * (a * d) ≡ b * c * 1 [MOD p]:= by exact Nat.ModEq.mul rfl hd

  -- Simplify
  simp at hd

  -- Use transitivity to conclude d ≡ b * c (mod p)
  exact Nat.ModEq.trans (id (Nat.ModEq.symm h)) hd
