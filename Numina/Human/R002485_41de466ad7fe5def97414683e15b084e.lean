import Mathlib

open Set

/-- In base $10$, the number $2013$ ends in the digit $3$. In base $9$, on the other hand, the same
number is written as $(2676)_{9}$ and ends in the digit $6$. For how many positive integers $b$
does the base-$b$-representation of $2013$ end in the digit $3$?


$\textbf{(A)}\ 6\qquad\textbf{(B)}\ 9\qquad\textbf{(C)}\ 13\qquad\textbf{(D)}\
16\qquad\textbf{(E)}\ 18$ -/
theorem number_theory_94122 :
    {b : ℕ | 0 < b ∧ (b.digits 2013).head! = 3}.ncard = 13 := by

  -- We claim that our set is just the set of numbers $b$ such that the remainder of $2013$ when
  -- divided by $b$ is $3$.
  have (b : ℕ) : (0 < b ∧ (b.digits 2013).head! = 3) ↔ 2013 % b = 3 := by
    -- For the left to right direction, assume that $b$ is a positive integer such that the last digit of
    -- $2013$ in base $b$ is $3$.
    constructor
    · rintro ⟨hb, h⟩

      -- $b$ cannot be equal to $1$ either because the last digit of $2013$ in base $1$ is $1$.
      have : 1 < b := by
        suffices b ≠ 1 by omega
        rintro rfl
        simp at h

      -- Actually, $b$ is greater than $3$ because the digits of a number in base $b$ are always less
      -- than $b$ when $b$ is greater than $1$.
      have : 3 < b := by
        rw [←h]
        apply Nat.digits_lt_base (m := 2013) ‹_›
        apply List.head!_mem_self
        rw [Nat.digits_ne_nil_iff_ne_zero]
        norm_num

      -- We know that the last digit of $2013$ in base $b$ is the remainder of $2013$ is congruent to
      -- 2013 module $b$. We also established that $3 < b$. Therefore, the remainder of 2013
      -- when divided by $b$ is $3$.
      convert (Nat.ofDigits_mod_eq_head! b (b.digits 2013))
      · rw [Nat.ofDigits_digits]
      · rw [h]
        exact (Nat.mod_eq_of_lt this).symm

    -- For the other direction, assume that the remainder of $2013$ when divided by $b$ is $3$.
    · intro h

      -- $b$ is positive because the remainder of $2013$ when divided by $0$ is undefined.
      have hb : 0 < b := by
        suffices b ≠ 0 by omega
        rintro rfl
        simp at h
      -- Now, let's show that the last digit of $2013$ in base $b$ is $3$.
      refine ⟨hb, ?_⟩

      -- As we said before, the last digit of $2013$ in base $b$ is congruent to $2013$ modulo $b$.
      -- So, it is enough to show that $3 < b$.
      symm
      convert (Nat.ofDigits_mod_eq_head! b (b.digits 2013))
      · rw [Nat.ofDigits_digits, h]
        -- This follows, because by assumption the remainder of $2013$ when divided by $b$ is $3$ and
        -- remainder is always less than the divisor.
      · symm
        apply Nat.mod_eq_of_lt
        apply Nat.digits_lt_base (m := 2013)
        · calc 1 < 3 := by norm_num
               _ = 2013 % b := by rw [h]
               _ < b := by exact Nat.mod_lt 2013 hb
        · apply List.head!_mem_self
          rw [Nat.digits_ne_nil_iff_ne_zero]
          norm_num

  -- So, our set is just the set of numbers $b$ such that the remainder of $2013$ when divided by $b$
  -- is $3$.
  simp_rw [this]

  -- We will show that the set of numbers $b$ such that the remainder of $2013$ when divided by $b$ is
  -- $3$ is the set of divisors of $2010$ except $1$, $2$, and $3$.
  have (b : ℕ) : 2013 % b = 3 ↔ b ∣ 2010 ∧ 3 < b := by
    -- For the left to right direction, assume that the remainder of $2013$ when divided by $b$ is $3$.
    constructor
    · intro h

      -- $b$ is positive because the remainder of $2013$ when divided by $0$ is undefined.
      have hb : 0 < b := by
        suffices b ≠ 0 by omega
        rintro rfl
        simp at h

      refine ⟨?_, ?_⟩
      -- The remainder and the divident are congruent modulo the divisor, so $2013$ and $3$ are
      -- congruent modulo $b$. This means that $b$ divides $2010$.
      · show b ∣ (2013 - 3)
        rw [←h]
        exact Nat.dvd_sub_mod 2013

      -- $b$ is greater than $3$ because the remainder is always less than the divisor.
      · rw [←h]
        exact Nat.mod_lt 2013 hb

    -- For the other direction, assume that $b$ divides $2010$ and $3 < b$.
    · rintro ⟨h, hb⟩
      have : 2010 % b = 0 := by exact Nat.dvd_iff_mod_eq_zero.mp h

      -- Because $2013 = 2010 + 3$, 2013 and 3 are congruent modulo $b$.
      show (2010 + 3) % b = 3
      rw [Nat.add_mod, this, zero_add, Nat.mod_mod_of_dvd 3 (dvd_refl b)]

      -- Because $b$ is greater than $3$, this implies that the remainder of $2013$ when divided by
      -- $b$ is $3$.
      exact Nat.mod_eq_of_lt hb

  -- So, our set is the set of divisors of $2010$ except $1$, $2$, and $3$.
  simp_rw [this]

  have : {b | b ∣ 2010 ∧ 3 < b} = {b ∈ (2010).divisors | 3 < b} := by ext b; simp
  rw [this]

  have : {b ∈ (2010).divisors | 3 < b} = (2010).divisors \ {1, 2, 3} := by
    ext b
    constructor
    · rintro ⟨hb1, hb2⟩
      refine ⟨hb1, ?_⟩
      simp; omega
    · rintro ⟨hb1, hb2⟩

      have : b ≠ 0 := by
        rintro rfl
        simp at hb1

      refine ⟨hb1, ?_⟩
      simp at hb2
      omega
  rw [this]

  -- Now, we need to count the number of divisors of $2010$. We will show that the number of divisors
  -- of $2010$ is $16$.
  suffices (2010).divisors.card = 16 from ?_
  · rw [Set.ncard_diff]
    · simp [this]
    · rintro _ (rfl | rfl | rfl)
      · simp
      · simp; norm_num
      · simp; norm_num

  -- The number of divisors of a number $n$ with the prime factorization $p_1^{e_1} \cdots p_k^{e_k}$
  -- is $(e_1 + 1) \cdots (e_k + 1)$.
  rw [Nat.card_divisors (by norm_num)]

  -- The prime factorization of $2010$ is $2 \cdot 3 \cdot 5 \cdot 67$. Therefore, the result
  -- follows.
  have : 2010 = 2 * 3 * 5 * 67 := by norm_num
  have : (2010).primeFactors = {2, 3, 5, 67} := by native_decide
  rw [this]
  simp [Finset.sum]
  have h2 : (2010).factorization 2 = 1 := by native_decide
  have h3 : (2010).factorization 3 = 1 := by native_decide
  have h4 : (2010).factorization 5 = 1 := by native_decide
  have h5 : (2010).factorization 67 = 1 := by native_decide
  rw [h2, h3, h4, h5]
  norm_num