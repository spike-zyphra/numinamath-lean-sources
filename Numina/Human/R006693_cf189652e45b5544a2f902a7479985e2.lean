import Mathlib
/- Let $M$ be an integer greater than 1. Let $a$ and $b$ be integers such that $a \ge b$.
If $a+b \equiv 2 \pmod M$ and $2a+b \equiv 1 \pmod M$, determine the smallest non-negative remainder of $a-b$ when divided by $M$. Show that this remainder is $(-4 \pmod M + M) \pmod M$. -/
theorem number_theory_640246 (m a b : ℤ) (hm : m > 1) (ha : a ≥ b) (h1 : a + b ≡ 2 [ZMOD m]) (h2 : 2 * a + b ≡ 1 [ZMOD m]) : (a - b) % m = (-(4 % m) + m) % m:= by
  -- Establish that 4 mod m is congruent to 4 (mod m)
  have g1 : 4 % m ≡ 4 [ZMOD m]:= by exact Int.mod_modEq 4 m
  -- Apply subtraction to both sides of the congruence
  replace g1 : 4 % m - (4 + 4 % m - m) ≡ 4 - (4 + 4 % m - m) [ZMOD m]:= by exact Int.ModEq.sub g1 rfl
  -- Simplify expressions using ring normalization
  ring_nf at g1
  rw [←g1]
  -- Rewrite 2*a + b as a + (a + b) using ring arithmetic
  rw [show 2 * a + b = a + (a + b) by ring] at h2
  -- Apply modular arithmetic properties to show a + (a + b) ≡ a + 2 (mod m)
  replace g1 : a + (a + b) ≡ a + 2 [ZMOD m]:= by exact Int.ModEq.add rfl h1
  -- Use transitivity to show a + 2 ≡ 1 (mod m)
  replace h2 : a + 2 ≡ 1 [ZMOD m]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h2)) g1)
  -- Add 2 to both sides of the congruence
  replace h1 : a + b + 2 ≡ 2 + 2 [ZMOD m]:= by exact Int.ModEq.add h1 rfl
  -- Normalize expressions using ring arithmetic
  ring_nf at h1 h2
  -- Prove that 1 + b ≡ 4 (mod m)
  replace h1 : 1 + b ≡ 4 [ZMOD m]:= by
    replace h2 : 2 + a + b ≡ 1 + b [ZMOD m]:= by exact Int.ModEq.add h2 rfl
    exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h1)) h2)
  -- Show (2 + a) - (1 + b) ≡ 1 - 4 (mod m)
  replace h1 : (2 + a) - (1 + b) ≡ 1 - 4 [ZMOD m]:= by exact Int.ModEq.sub h2 h1
  -- Normalize using ring arithmetic
  ring_nf at h1
  -- Add and subtract 1 to maintain equivalence
  replace h1 : 1 + (a - b) + -1 ≡ -3 + -1 [ZMOD m]:= by exact Int.ModEq.add h1 rfl
  -- Final normalization
  ring_nf at h1
  -- Apply the congruence
  rw [h1]
  -- Simplify the final expression
  simp
