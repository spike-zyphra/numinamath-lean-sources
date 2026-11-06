import Mathlib

/- Lemma 1: If natural numbers $a, b$ satisfy $a^2 + b^2 = 1$, then $a + b = 1$. -/
def lemma_1 {a b : ℕ} (h : a ^ 2 + b ^ 2 = 1) : a + b = 1 := by
  -- Clearly, $a, b \leq 1$.
  have ha : a ≤ 1 := by nlinarith
  have hb : b ≤ 1 := by nlinarith
  -- We discuss the cases $a = 0, 1$ and $b = 0, 1$ separately.
  interval_cases a <;> interval_cases b
  all_goals
    simp at *

/- Lemma 2: If natural numbers $a, b$ satisfy $4 \mid a^2 + b^2$, then $2 \mid a$ and $2 \mid b$. -/
def lemma_2 {a b : ℕ} (h : 4 ∣ a ^ 2 + b ^ 2) : 2 ∣ a ∧ 2 ∣ b := by
  -- We discuss the cases $a, b$ are even or odd separately.
  -- Set $a = 2a' + r$ and $b = 2b' + s$ for some natural numbers $a', b'$ and $r, s \in \{0, 1\}$.
  rcases Nat.even_or_odd a with ⟨a', rfl⟩ | ⟨a', rfl⟩
  . rcases Nat.even_or_odd b with ⟨b', rfl⟩ | ⟨b', rfl⟩
    . -- When a and b are both even, the conclusion holds.
      exact ⟨⟨a', by ring⟩, ⟨b', by ring⟩⟩
    . -- When a is even and b is odd, we have $4 \mid 4 * (a'^2 + b'^2 + b') + 1$ from the assumption.
      replace h : 4 ∣ 4 * (a' ^ 2 + b' ^ 2 + b') + 1 := by
        convert h using 1
        ring
      -- It is impossible.
      omega
  . -- When a is odd and b is even, we have $4 \mid 4 * (a'^2 + b'^2 + a') + 1$ from the assumption.
    rcases Nat.even_or_odd b with ⟨b', rfl⟩ | ⟨b', rfl⟩
    . replace h : 4 ∣ 4 * (a' ^ 2 + b' ^ 2 + a') + 1 := by
        convert h using 1
        ring
      -- It is impossible.
      omega
    . -- When a is odd and b is odd, we have $4 \mid 4 * (a'^2 + b'^2 + a' + b') + 2$ from the assumption.
      replace h : 4 ∣ 4 * (a' ^ 2 + b' ^ 2 + a' + b') + 2 := by
        convert h using 1
        ring
      -- It is impossible.
      omega

/- Lemma 3: If $p$ is a prime number and $p \equiv 3 \pmod 4$, then $p \mid a^2 + b^2$ only if $p \mid a$ and $p \mid b$. -/
def lemma_3 {a b p : ℕ} (hp₁ : p.Prime) (hp₂ : p ≡ 3 [MOD 4]) (h : p ∣ a ^ 2 + b ^ 2) : p ∣ a ∧ p ∣ b := by
  have inst : Fact p.Prime := ⟨hp₁⟩
  simp [Nat.ModEq] at hp₂
  -- We have: the Legendre symbol $\left(\frac{-1}{p}\right) = -1$.
  -- Since $p$ is a prime number and $p \equiv 3 \pmod 4$
  replace hp₂ : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_three_mod_four hp₂]
  -- We have: $p \mid a^2 - (-1) * b^2$.
  replace h : (p : ℤ) ∣ (a : ℤ) ^ 2 - (-1) * (b : ℤ) ^ 2 := by
    simp
    norm_cast
  -- We apply the library lemma, which asserts:
  -- If `legendreSym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x` and `y`.
  have H := legendreSym.prime_dvd_of_eq_neg_one (p := p) hp₂ h
  norm_cast at H

/- Let $x$ be an integer from $\{0, 1, 2, 3\}$.
Determine for which values of $x$ the following statement is true:
"For any natural numbers $a, b, c, k$ and any prime natural number $p$, if $a,b,c$ form a Pythagorean triple (i.e. $a^2+b^2=c^2$), $c=p^k$, and $p \equiv x \pmod 4$, then $a+b=c$."
Show that the statement is true if $x \in \{0, 2, 3\}$. -/
theorem number_theory_636128 : {x : ℕ | x ∈ ({0, 1, 2, 3} : Set ℕ) ∧ ∀ a b c k p, a^2 + b^2 = c^2 → c = p^k → p.Prime → p ≡ x [MOD 4] → a + b = c} = {0, 2, 3} := by
  ext x
  simp
  -- We can assume $x$ is one of $0, 1, 2, 3$.
  wlog hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3
  . itauto
  rcases hx with rfl | rfl | rfl | rfl <;> simp
  . -- When $x = 0$, we have $p \equiv 0 \pmod 4$.
    intro a b c k p h hc hp₁ hp₂
    rw [Nat.modEq_zero_iff_dvd] at hp₂
    -- So $p$ is even.
    have hp₃ : 2 ∣ p := (show 2 ∣ 4 by norm_num).trans hp₂
    -- Thus $p = 2$. Contradiction.
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp₁] at hp₃
    norm_num [← hp₃] at hp₂
  . -- When $x = 1$, we have $p \equiv 1 \pmod 4$.
    -- We have a counter-example: $3^2 + 4^2 = 5^2$.
    use 3, 4, 5, by simp, 1, 5
    decide
  . -- When $x = 2$, we have $p \equiv 2 \pmod 4$.
    intro a b c k p h hc hp₁ hp₂
    simp [Nat.ModEq] at hp₂
    -- So $p$ is even, and thus $p = 2$.
    have hp₃ : 2 ∣ p := by omega
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp₁] at hp₃
    subst p c
    clear hp₁ hp₂
    -- We prove the statement by induction on $k$.
    induction k generalizing a b with
    | zero =>
      -- When $k = 0$, we have $a^2 + b^2 = 1$.
      -- We apply Lemma 1.
      exact lemma_1 h
    | succ k ih =>
      -- Suppose the statement holds for $k$.
      -- For the case of $k + 1$, we have $4 \mid a^2 + b^2$.
      have h' : 4 ∣ a ^ 2 + b ^ 2 := by
        simp [h, pow_succ 2, mul_pow]
      -- We have $2 \mid a$ and $2 \mid b$ by Lemma 2.
      -- So $a = 2a'$ and $b = 2b'$.
      rcases lemma_2 h' with ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
      rw [pow_succ 2] at h ⊢
      rw [mul_pow, mul_pow, mul_pow] at h
      -- We have: $a'^2 + b'^2 = 2^k$.
      replace h : a' ^ 2 + b' ^ 2 = (2 ^ k) ^ 2 := by omega
      -- It suffices to show that $a' + b' = 2^k$.
      suffices a' + b' = 2 ^ k by omega
      -- By the induction hypothesis, we are done.
      exact ih a' b' h
  . -- When $x = 3$, we have $p \equiv 3 \pmod 4$.
    intro a b c k p h hc hp₁ hp₂
    subst c
    -- The proof is similar to the case of $x = 2$.
    induction k generalizing a b with
    | zero =>
      exact lemma_1 h
    | succ k ih =>
      have h' : p ∣ a ^ 2 + b ^ 2 := by
        simp [h, pow_succ p]
        exact dvd_pow (by simp) (by simp)
      rcases lemma_3 hp₁ hp₂ h' with ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
      rw [pow_succ p] at h ⊢
      rw [mul_pow, mul_pow, mul_pow] at h
      replace h : a' ^ 2 + b' ^ 2 = (p ^ k) ^ 2 := by
        apply Nat.mul_left_cancel (show 0 < p ^ 2 from Nat.pow_pos hp₁.pos)
        linear_combination h
      suffices a' + b' = p ^ k by linear_combination p * this
      exact ih a' b' h
