import Mathlib

open Nat Set

/-- Let $n$ be the smallest positive integer such that $n$ is divisible by $20$, $n^2$ is a perfect
cube, and $n^3$ is a perfect square. What is the number of digits of $n$?

$\textbf{(A)}\ 3 \qquad \textbf{(B)}\ 4 \qquad \textbf{(C)}\ 5 \qquad \textbf{(D)}\ 6 \qquad
\textbf{(E)}\ 7$ -/
theorem number_theory_94477 {n : ℕ} {s : Set ℕ} (hs : s = {n : ℕ | n ≠ 0 ∧  20 ∣ n ∧ (∃ m, n = m^2) ∧ (∃ m, n = m^3)})
    (hsn : IsLeast s n) : (digits 10 n).length = 7 := by

  -- Before starting our proof, we will prove an important lemma. This lemma says that $n$ is a
  -- perfect $k$-th power iff for all prime factors $p$ of $n$, the exponent of $p$ in the prime
  -- factorization of $n$ is divisible by $k$.
  have exists_eq_pow_iff_dvd_factorization {k n : ℕ} (hk : k ≠ 0) :
      (∃ m, n = m^k) ↔ (∀ p ∈ n.primeFactors, k ∣ n.factorization p) := by
    -- For $n = 0$, the statement is trivial. So, we will assume $n \neq 0$.
    by_cases hn : n = 0
    · subst hn
      simp; use 0; simp [hk]

    constructor

    -- For the left to right direction, assume that $n = m^k$ for some $m$. Let $p$ be a prime factor
    -- of $n$.
    · rintro ⟨m, rfl⟩ p hp

      -- Then, the number of $p$ factors in $n$ is $k$ times the number of $p$ factors in $m$.
      rw [Nat.factorization_pow]
      simp

    -- For the other direction, assume that for all prime factors $p$ of $n$, the exponent of $p$ in
    -- the prime factorization of $n$ is divisible by $k$. Let $A$ be the set of all prime factors of
    -- $n$. We denote the number of number of $p$ factors in $n$ by $a_n$. Then,
    -- $n = \prod_{p \in A} p^{a_n}$.
    · intro h
      -- Let $m = \prod_{p \in A} p^{a_n / k}$.
      let m := ∏ p ∈ n.primeFactors, p^((n.factorization p) / k)
      use m
      symm
      -- We can do this because each $a_n$ is divisible by $k$ by assumption.
      have (p : ℕ) (hp : p ∈ n.primeFactors) : n.factorization p / k * k = n.factorization p := by
        rw [Nat.div_mul_cancel (h p hp)]

      -- Then, $m^k = n$ by simple algebra.
      calc _ = (∏ p ∈ n.primeFactors, p^((n.factorization p) / k))^k := by rfl
          _ = ∏ p ∈ n.primeFactors, (p^((n.factorization p) / k))^k := by rw [Finset.prod_pow]
          _ = ∏ p ∈ n.primeFactors, p^((n.factorization p) / k * k) := by simp_rw [pow_mul]
          _ = ∏ p ∈ n.primeFactors, p^(n.factorization p) := by apply Finset.prod_congr; rfl; intro p hp; congr; rw [Nat.div_mul_cancel (h p hp)]
          _ = _ := by rw [←Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_pow_eq_self hn]

  -- Now, we will prove the main result. Let $s$ be the set of all positive integers $n$ such that
  -- $20$ divides $n$, $n$ is a perfect square, and $n$ is a perfect cube.

  -- We claim that $n = 10^6$, so $n$ has $7$ digits.
  suffices n = 10^6 by simp [this]

  -- First, we will simplify the definition of $s$. We claim that for a natural number $n$, $n$ is a
  -- perfect square and a perfect cube iff it is a perfect $6$-th power.
  have {n : ℕ} : (∃ m, n = m^2) ∧ (∃ m, n = m^3) ↔ (∃ m, n = m^6) := by
    -- To prove this, first write down everything in terms of prime factorizations using our lemma.
    rw [exists_eq_pow_iff_dvd_factorization (by norm_num),
        exists_eq_pow_iff_dvd_factorization (by norm_num),
        exists_eq_pow_iff_dvd_factorization (by norm_num)]

    -- So, we need to show that for all prime factors $p$ of $n$, $6$ divides the exponent of $p$ in
    -- the prime factorization of $n$ iff $2$ and $3$ divide the exponent of $p$ in the prime
    -- factorization of $n$. However, this is trivial because $6 = 2 \cdot 3$ and $2$ and $3$ are
    -- coprime.
    constructor
    · rintro ⟨h1, h2⟩
      intro p hp
      have := h1 p hp
      have := h2 p hp
      omega
    · intro h
      constructor <;>{
        intro p hp
        specialize h p hp
        omega
      }

  -- With this simplification, we can write down $s$ in a simpler form:
  -- $s = \{n \mid n \neq 0 \land 20 \mid n \land \exists m, n = m^6\}$. We will simplify this
  -- further.
  simp_rw [this] at hs

  -- Of course, we can take the existential quantifier to the left and write:
  -- $s = \{n \mid \exists m, m \neq 0 \land 20 \mid m^6 \land n = m^6\}$.
  have {n : ℕ} : (n ≠ 0 ∧ 20 ∣ n ∧ ∃ m, n = m^6) ↔ (∃ m, m ≠ 0 ∧ 20 ∣ m^6 ∧ n = m^6) := by
    constructor
    · rintro ⟨h1, h2, m, h3⟩
      refine ⟨m, ?_, h3 ▸ h2, h3⟩
      intro h
      apply h1
      simp [h3]
      assumption
    · rintro ⟨m, h1, h2, h3⟩
      exact ⟨by simp [h3, h1], h3 ▸ h2, m, h3⟩
  simp_rw [this] at hs

  -- For a further simplification, we will show that for a natural number $a$, $20$ divides $a^6$ iff
  -- $10$ divides $a$.
  have {a : ℕ} : 20 ∣ a^6 ↔ 10 ∣ a := by
    show (2^2 * 5) ∣ a^6 ↔ (2 * 5) ∣ a
    constructor
    -- For the left to right direction, assume that $20$ divides $a^6$. We need to show that $10$
    -- divides $a$.
    · intro h
      -- Because $10 = 2 \cdot 5$ and $2$ and $5$ are coprime, it is enough to show that $2$ divides
      -- $a$ and $5$ divides $a$.
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)

      -- Because $2$ is prime, we can instead show that $2$ divides $a^6$ which is immediate because
      -- $20$ divides $a^6$.
      · apply Nat.Prime.dvd_of_dvd_pow (n := 6) (by norm_num) (by omega)
      -- Similarly, we can show that $5$ divides $a$.
      · apply Nat.Prime.dvd_of_dvd_pow (n := 6) (by norm_num) (by omega)

    -- For the other direction, assume that $10$ divides $a$.
    · intro h
      -- Because $20 = 2^2 \cdot 5$ and $2$ and $5$ are coprime, it is enough to show that $2^2$
      -- divides $a^6$ and $5$ divides $a^6$.
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      -- We know that $2$ divides $a$ so $2^2$ divides $a^2$. Therefore, $2^2$ divides $a^6$.
      · replace h : 2 ∣ a := by omega
        calc _ ∣ a^2 := by exact pow_dvd_pow_of_dvd h 2
             _ ∣ (a^2)^3 := by exact Dvd.intro_left ((a ^ 2).pow 2) rfl
             _ = _ := by ring
      -- For $5$, we know that $5$ divides $a$ so $5$ divides $a^6$.
      · calc _ ∣ 2 * 5 := by norm_num
             _ ∣ a := by assumption
             _ ∣ _ := by exact Dvd.intro_left (a.pow 5) rfl

  -- With this simplification, we can write down $s$ in a simpler form:
  -- $s = \{n \mid \exists m, m ≠ 0 \land 10 \mid m \land n = m^6\}$.
  simp_rw [this] at hs

  -- Let $t$ be the set of all positive integers divisible by $10$.
  let t := {m | m ≠ 0 ∧ 10 ∣ m}

  -- Let $f : \mathbb{N} \to \mathbb{N}$ be the function $f(m) = m^6$.
  let f (m : ℕ) := m^6

  -- From the simple form of $s$, it is clear that $s$ is just the image of $t$ under $f$.
  replace hs : s = f '' t := by
    ext n
    constructor
    · intro hn
      simp only [hs] at hn
      rcases hn with ⟨a, ha1, ha2, hna⟩
      exact ⟨a, ⟨ha1, ha2⟩, hna.symm⟩
    · rintro ⟨a, ⟨ha1, ha2⟩, han⟩
      simp only [hs]
      exact ⟨a, ha1, ha2, han.symm⟩

  -- Moreover, $f$ is monotone because power functions are monotone.
  have : Monotone f := by
    intro a b h
    simp [f]
    gcongr

  -- Therefore, it is enough to show that the least element of $t$ is $10$ because $f$ maps $10$ to
  -- $10^6$.
  suffices IsLeast t 10 from ?_
  · have := Monotone.map_isLeast ‹_› this
    rw [hs] at hsn
    apply IsLeast.unique hsn this
  clear * - t

  -- Let's show this and complete our proof.
  constructor
  -- Obviously $10$ is in $t$.
  · simp [t]
  -- Let $n$ be another element of $t$. It is nonzero and divisible by $10$. Therefore, it is greater
  -- than or equal to $10$. Therefore, $10$ is the smallest element of $t$.
  · intro n ⟨hn1, hn2⟩
    exact le_of_dvd (by omega) hn2