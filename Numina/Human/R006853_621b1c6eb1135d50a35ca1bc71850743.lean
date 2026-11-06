import Mathlib

lemma lemma_even
  (n : ℕ)
  (hn : Even n)
  : 9^n ≡ 1 [ZMOD 5] :=
by
  have : 9 ≡ -1 [ZMOD 5] := by rfl
  have : 9^n ≡ (-1) ^ n [ZMOD 5] := by
    exact Int.ModEq.pow n this
  have r : (- 1)^n = 1 := by exact Even.neg_one_pow hn
  rw [r] at this
  assumption

lemma lemma_odd
  (n : ℕ)
  (hn : Odd n)
  : 9^n ≡ -1 [ZMOD 5] :=
by
  have : 9 ≡ -1 [ZMOD 5] := by rfl
  have : 9^n ≡ (-1) ^ n [ZMOD 5] := by
    exact Int.ModEq.pow n this
  have r : (- 1)^n = -1 := by exact Odd.neg_one_pow hn
  rw [r] at this
  assumption

/- Let $a, b, c, d, e$ be integers between 0 and 8 inclusive. Let $N$ be the number whose base-nine representation is given by the list of digits $[a,b,c,d,e]$, where $a$ is the most significant digit (i.e., $N = a \cdot 9^4 + b \cdot 9^3 + c \cdot 9^2 + d \cdot 9^1 + e \cdot 9^0$). Show that the remainder when $N$ is divided by 5 is $(a-b+c-d+e) \pmod 5$. -/
theorem number_theory_641738
  (a b c d e : ℕ)
  (ha : a ≤ 8)
  (hb : b ≤ 8)
  (hc : c ≤ 8)
  (hd : d ≤ 8)
  (he : e ≤ 8)
  : a * 9 ^ 4 + b * 9 ^ 3 + c * 9 ^ 2 + d * 9 ^ 1 + e * 9 ^ 0
  ≡ a - b + c - d + e [ZMOD 5] :=
by
  -- Idea is using the lemma we have proven, to rewrite each sub term.
  trans ↑a * 9 ^ 4 + ↑b * 9 ^ 3 + ↑c * 9 ^ 2 + ↑d * 9 ^ 1 + ↑e
  . simp
  apply Int.ModEq.add_right
  trans ↑a * 9 ^ 4 + ↑b * 9 ^ 3 + ↑c * 9 ^ 2 + ↑d * (- 1)
  . apply Int.ModEq.add_left
    apply Int.ModEq.mul_left
    apply lemma_odd
    simp
  rw [show ∀ a, a + d * (-1:ℤ) = a - d by omega]
  apply Int.ModEq.sub_right
  trans ↑a * 9 ^ 4 + ↑b * 9 ^ 3 + ↑c
  . apply Int.ModEq.add_left
    conv => rhs; rw [show (c : ℤ) = c * 1 by simp]
    apply Int.ModEq.mul_left
    apply lemma_even
    simp
  apply Int.ModEq.add_right
  trans ↑a * 9 ^ 4 - ↑b
  . apply Int.ModEq.add_left
    rw [show - (b : ℤ) = b * (- 1) by omega]
    apply Int.ModEq.mul_left
    apply lemma_odd
    decide
  apply Int.ModEq.sub_right
  conv => rhs; rw [←Int.mul_one a]
  apply Int.ModEq.mul_left
  apply lemma_even
  decide
