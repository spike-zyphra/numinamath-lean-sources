import Mathlib

/- We have positive integers $a,$ $b,$ and $c$ such that $a > b > c.$ When $a,$ $b,$ and $c$ are divided by $19$, the remainders are $4,$ $2,$ and $18,$ respectively.

When the number $2a + b - c$ is divided by $19$, what is the remainder? -/
theorem number_theory_22993 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a > b ∧ b > c) (hmod : a % 19 = 4 ∧ b % 19 = 2 ∧ c % 19 = 18) :
    (2 * a + b - c) % 19 = 11 := by
  show 2 * a + b - c ≡ 11 [ZMOD 19]
  have amod : a ≡ 4 [ZMOD 19] := by
    exact hmod.1
  have bmod : b ≡ 2 [ZMOD 19] := by
    exact hmod.2.1
  have cmod : c ≡ 18 [ZMOD 19] := by
    exact hmod.2.2
  apply Int.ModEq.mul_left 2 at amod
  have mod1 : 2 * a + b ≡ 2 * 4 + 2 [ZMOD 19] := by
    exact Int.ModEq.add amod bmod
  have mod2 : 2 * a + b - c ≡ 2 * 4 + 2 - 18 [ZMOD 19] := by
    exact Int.ModEq.sub mod1 cmod
  exact mod2
