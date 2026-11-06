import Mathlib

open Nat

/-- A positive integer divisor of $12!$ is chosen at random. The probability that the divisor
chosen is a perfect square can be expressed as $\frac{m}{n}$, where $m$ and $n$ are relatively
prime positive integers. What is $m+n$?

$\textbf{(A)}\ 3\qquad\textbf{(B)}\ 5\qquad\textbf{(C)}\ 12\qquad\textbf{(D)}\ 1
8\qquad\textbf{(E)}\ 23$ -/
theorem number_theory_97662 (A : Finset ℕ) (hA : A = {n ∈ divisors (12 !) | IsSquare n}) :
    (A.card : ℚ) / (divisors (12 !)).card = 1 / 22 := by

  -- Before proceeding, let's remember some basic facts about number theory.
  -- First, remember that if $n$ divides $m$, then the set of prime factors of $n$ is a subset of the
  -- set of prime factors of $m$.
  have primeFactors_mono {n m : ℕ} (hnm : n ∣ m) (hm : m ≠ 0) : n.primeFactors ⊆ m.primeFactors := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    refine ⟨hp.1, ?_, hm⟩
    calc _ ∣ n := by exact hp.2.1
          _ ∣ m := by exact hnm

  -- Second, remember that $n$ is a square if and only if the number of $p$ factors in $n$ is even
  -- for every prime $p$.
  have isSquare_iff_factorization_even (n : ℕ) : IsSquare n ↔ ∀ p, Even (n.factorization p) := by
    constructor
    · intro h
      rw [isSquare_iff_exists_sq] at h
      rcases h with ⟨m, rfl⟩
      simp
    · intro h

      by_cases hn : n = 0
      · simp [hn]

      let m := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
      rw [isSquare_iff_exists_sq]
      use m
      calc _ = n.factorization.prod (fun p e ↦ p ^ e) := by rw [Nat.factorization_prod_pow_eq_self hn]
          _ = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by rw[Nat.prod_factorization_eq_prod_primeFactors]
          _ = ∏ p ∈ n.primeFactors, p ^ ((n.factorization p / 2) * 2) := ?_
          _ = ∏ p ∈ n.primeFactors, (p ^ (n.factorization p / 2)) ^ 2 := by simp_rw [Nat.pow_mul]
          _ = (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) ^ 2 := by rw [Finset.prod_pow]
          _ = m ^ 2 := by rfl

      apply Finset.prod_congr rfl
      intro p hp
      congr
      exact Eq.symm (Nat.div_two_mul_two_of_even (h p))

  -- Let $A$ be the set of square divisors of $12!$.

  -- The prime factorization of $12!$ is $2^{10} \cdot 3^5 \cdot 5^2 \cdot 7 \cdot 11$.
  have twelve_factorial_eq_prod_prime_pow : 12 ! = 2 ^ 10 * 3 ^ 5 * 5 ^ 2 * 7 * 11 := by decide

  have twelve_factorial_ne_zero : 12 ! ≠ 0 := by decide

  have twelve_factorial_primeFactors : (12 !).primeFactors = {2, 3, 5, 7, 11} := by
    simp (discharger := norm_num) [-reduceMul, -reducePow, twelve_factorial_eq_prod_prime_pow,
      primeFactors_mul, primeFactors_pow, Nat.Prime.primeFactors]
    rfl

  have twelve_factorial_factorization : (12 !).factorization =
      Finsupp.single 2 10 + Finsupp.single 3 5 + Finsupp.single 5 2 + Finsupp.single 7 1 +
      Finsupp.single 11 1 := by
    simp (discharger := norm_num) [-reduceMul, -reducePow, twelve_factorial_eq_prod_prime_pow,
      Nat.Prime.factorization]

  -- This yields a total of $11 \cdot 6 \cdot 3 \cdot 2 \cdot 2$ divisors of $12!.$
  have twelve_factorial_divisors_card : (divisors (12 !)).card = 11 * 6 * 3 * 2 * 2 := by
    rw [card_divisors (by apply factorial_ne_zero), twelve_factorial_primeFactors,
      twelve_factorial_factorization]
    simp

  -- Therefore, it sufficios to prove that the set of square divisors of $12!$ has $22$ elements.
  suffices A.card = 36 by simp [this, twelve_factorial_divisors_card]; norm_num

  -- Let $s$ be the set of all finitely supported functions from $\mathbb{N}$ to $\mathbb{N}$ such that
  -- the support of the function is a subset of $\{2, 3, 5\}$, and the value of the function at $2$, $3$,
  -- and $5$ is at most $10$, $5$, and $2$, respectively. Moreover, the value of the function at $2$,
  -- $3$, and $5$ is even.
  let s := {v : ℕ →₀ ℕ | v.support ⊆ {2, 3, 5} ∧
    v 2 ≤ 10 ∧ v 3 ≤ 5 ∧ v 5 ≤ 2 ∧ Even (v 2) ∧ Even (v 3) ∧ Even (v 5)}

  -- Let $f$ be the function that maps a finitely supported function from $\mathbb{N}$ to
  -- $\mathbb{N}$ to its product with the power map.
  let f : (ℕ →₀ ℕ) → ℕ := fun v ↦ v.prod (fun p e => p ^ e)

  -- Let $g$ be the function that maps a natural number to its factorization tought of as a finitely
  -- supported function.
  let g : ℕ → (ℕ →₀ ℕ) := fun n ↦ n.factorization

  -- We claim that $f$ is the left inverse of $g$ on the set of positive natural numbers. To see
  -- this, let $n$ be a positive natural number. We need to show that $f(g(n)) = n$. However, this
  -- is just the fundamental theorem of arithmetic.
  have f_circ_g {n} (hn : n ≠ 0) : f (g n) = n := by
    simp [f, g]
    rw [Nat.factorization_prod_pow_eq_self hn]

  -- Moreover, we claim that $g$ is the left inverse of $f$ on the finitely supported functions
  -- whose supports are subsets of primes. To see this, let $v$ be a finitely
  -- supported function from $\mathbb{N}$ to $\mathbb{N}$ whose support is a subset of primes. We
  -- need to show that $g(f(v)) = v$.
  have g_circ_f {v} (hv : v.support ⊆ {p : ℕ | p.Prime}) : g (f v) = v := by
    simp [f, g]

    -- Factorization converts multiplication to addition provided that the terms multiplying are
    -- non-zero.
    show (∏ p ∈ v.support, p^(v p)).factorization = v
    apply Finsupp.ext
    intro
    rw [Nat.factorization_prod]; swap
    · intro p hp
      simp [(hv hp).ne_zero]
    congr

    simp
    have : ∑ x ∈ v.support, v x • x.factorization = ∑ x ∈ v.support, v x • (fun₀ | x => 1) := by
      apply Finset.sum_congr
      · rfl
      · intro q hq
        congr
        rw [Nat.Prime.factorization]
        apply hv hq

    simp_rw [this, Finsupp.smul_single, smul_eq_mul, mul_one]
    show v.sum Finsupp.single = v
    apply Finsupp.sum_single

  -- We will show that the sets $s$ and $A$ are in bijection via $f$ and $g$.
  suffices s.ncard = 36 from ?_

  · rw [←this, ←Set.ncard_coe_Finset]
    apply Set.ncard_congr (fun n _ ↦ g n)
    -- First, let's show that $g$ maps $A$ to $s$. Let $n \in A$.
    · intro n hn
      simp [hA, ‹12 ! ≠ 0›] at hn
      rcases hn with ⟨hn1, hn2⟩

      have : n ≠ 0 := by rintro rfl; simp at hn1; apply ‹12 ! ≠ 0›; exact hn1

      -- Because $n$ divides $12!$, the set of prime factors of $n$ is a subset of the set of prime
      -- factors of $12!$ which is $\{2, 3, 5, 7, 11\}$.
      have hn3 : n.primeFactors ⊆ {2, 3, 5, 7, 11} := by
        rw [←twelve_factorial_primeFactors]
        apply primeFactors_mono hn1 ‹12 ! ≠ 0›

      -- Moreover, number of primes in the prime factorization of $n$ is less than or equal to the
      -- number of primes in the prime factorization of $12!$.
      rw [←Nat.factorization_le_iff_dvd ‹n ≠ 0› ‹12 ! ≠ 0›] at hn1

      -- Therefore, we have the number of 2, 3, 5, 7, and 11 factors in the prime factorization of
      -- $n$ are at most 10, 5, 2, 1, and 1, respectively.
      have : n.factorization 2 ≤ 10 := by
        specialize hn1 2
        convert hn1
        simp [twelve_factorial_factorization]
      have : n.factorization 3 ≤ 5 := by
        specialize hn1 3
        convert hn1
        simp [twelve_factorial_factorization]
      have : n.factorization 5 ≤ 2 := by
        specialize hn1 5
        convert hn1
        simp [twelve_factorial_factorization]
      have : n.factorization 7 ≤ 1 := by
        specialize hn1 7
        convert hn1
        simp [twelve_factorial_factorization]
      have : n.factorization 11 ≤ 1 := by
        specialize hn1 11
        convert hn1
        simp [twelve_factorial_factorization]

      -- However, we know that $n$ is a square, so the number prime factors in the prime factorization
      -- of $n$ is even for every prime.
      rw [isSquare_iff_factorization_even] at hn2
      have : Even (n.factorization 2) := by exact hn2 2
      have : Even (n.factorization 3) := by exact hn2 3
      have : Even (n.factorization 5) := by exact hn2 5
      have : Even (n.factorization 7) := by exact hn2 7
      have : Even (n.factorization 11) := by exact hn2 11

      -- This implies that the number of 7 and 11 factors in the prime factorization of $n$ is zero.
      -- Because they are less than or equal to 1 and even.
      have : n.factorization 7 = 0 := by
        interval_cases n.factorization 7
        · rfl
        · simp at this
      have : n.factorization 11 = 0 := by
        interval_cases n.factorization 11
        · rfl
        · simp at this

      -- Then, 7 and 11 are actually not in the prime factorization of $n$.
      have : n.primeFactors ⊆ {2, 3, 5} := by
        intro p hp
        have hp' : p ∈ ({2, 3, 5, 7, 11} : Finset ℕ) := by exact hn3 hp
        simp at hp'
        rcases hp' with (rfl | rfl | rfl | rfl | rfl)
        · simp
        · simp
        · simp
        · exfalso
          simp at hp
          have := Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1
          rw [‹n.factorization 7 = 0›] at this
          linarith only [this]
        · exfalso
          simp at hp
          have := Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1
          rw [‹n.factorization 11 = 0›] at this
          linarith only [this]

      -- These show that $n$ is in the set $s$.
      simp [g, s]
      split_ands <;> assumption

    -- Now, let's show that $g$ is injective on $A$. Let $n, m \in A$. Assume that $g(n) = g(m)$.
    -- Because $f$ is the left inverse of $g$ on the set of positive natural numbers, and $n$, $m$
    -- are positive, we have $f(g(n)) = f(g(m))$. This implies $n = m$.
    · intro n m hn hm h
      apply_fun f at h
      simp [hA] at hn
      replace hn := hn.1.1
      replace hn : n ≠ 0 := by rintro rfl; simp at hn; apply ‹12 ! ≠ 0›; exact hn
      simp [hA] at hm
      replace hm := hm.1.1
      replace hm : m ≠ 0 := by rintro rfl; simp at hm; apply ‹12 ! ≠ 0›; exact hm
      simpa [f_circ_g, hn, hm] using h

    -- Now, let's show that $g$ is surjectivean $A$. Let $v \in s$. We need to show that there exists
    -- $n \in A$ such that $g(n) = v$. Choosing $n$ to be the product of the power map with $v$
    -- works because $g$ and $f$ are inverses of each other under appropriate hypothesis.
    · intro v hv
      rcases hv with ⟨hv, _, _, _, _, _, _⟩
      use (f v)
      simp [g_circ_f]

      simp [hA, ‹12 ! ≠ 0›]
      split_ands
      · simp [f]
        rw [←Nat.factorization_prod_pow_eq_self ‹12 ! ≠ 0›]
        apply Finsupp.prod_dvd_prod_of_subset_of_dvd
        · calc _ ⊆ {2, 3, 5} := hv
               _ ⊆ _ := ?_
          intro p
          simp_intro hp
          rcases hp with (rfl | rfl | rfl) <;> simp only [factorial_succ] <;> norm_num
        · intro p hp
          apply Nat.pow_dvd_pow
          have : p ∈ ({2, 3, 5} : Finset ℕ) := by exact hv hp
          simp at this
          rcases this with (rfl | rfl | rfl) <;>
          simpa [twelve_factorial_factorization]

      · rw [isSquare_iff_factorization_even]
        intro p

        have : (f v).factorization = v := by
          calc _ = g (f v) := by simp [g]
               _ = _ := ?_

          have : ↑v.support ⊆ ({p : ℕ | p.Prime} : Set ℕ) := by
            calc _ ⊆ ↑({2, 3, 5} : Finset ℕ) := by exact hv
                 _ ⊆ {p : ℕ | p.Prime} := ?_
            simp
            rintro p (rfl | rfl | rfl) <;> norm_num

          simp [g_circ_f, this]
        rw [this]

        by_cases hp : ¬ p ∈ v.support
        · simp at hp; simp [hp]
        simp only [ne_eq, Decidable.not_not] at hp
        have : p ∈ ({2, 3, 5} : Finset ℕ) := by exact hv hp
        simp at this
        rcases this with (rfl | rfl | rfl) <;> assumption

      · have : ↑v.support ⊆ {p : ℕ | p.Prime} := by
          calc _ ⊆ ↑({2, 3, 5} : Finset ℕ) := by exact hv
               _ ⊆ {p : ℕ | p.Prime} := ?_
          simp
          rintro p (rfl | rfl | rfl) <;> norm_num
        simp [g_circ_f, this]


  -- Now, we need to show that the cardinality of $s$ is $36$.
  -- To that end, let $t$ be the set of all triples of natural numbers $(a, b, c)$ such that $a \leq 10$,
  -- $b \leq 5$, $c \leq 2$, and $a$, $b$, and $c$ are even.
  let t := (Finset.filter Even (Finset.Iic 10)) ×ˢ (Finset.filter Even (Finset.Iic 5)) ×ˢ (Finset.filter Even (Finset.Iic 2))

  -- We will show that the sets $s$ and $t$ are in bijection via $f$ and $g$ where $f$ is the function
  -- that maps a triple $(a, b, c)$ to the finitely supported function that maps $2$, $3$, and $5$ to
  -- $a$, $b$, and $c$, respectively, and $g$ is the function that maps a finitely supported function
  -- to the triple of values at $2$, $3$, and $5$.
  let f : (ℕ × ℕ × ℕ) → (ℕ →₀ ℕ) := fun ⟨a, b, c⟩ ↦ Finsupp.single 2 a + Finsupp.single 3 b + Finsupp.single 5 c
  let g : (ℕ →₀ ℕ) → (ℕ × ℕ × ℕ) := fun v ↦ (v 2, v 3, v 5)

  -- First, let's show that $f$ is the left inverse of $g$ on the set of finitely supported functions
  -- with support a subset of $\{2, 3, 5\}$.
  have f_circ_g {v} (hv : v.support ⊆ {2, 3, 5}) : f (g v) = v := by
    simp [f, g]
    apply Finsupp.ext
    intro p

    by_cases hp : p ∈ ({2, 3, 5} : Finset ℕ)
    · simp at hp
      simp [hp]
      rcases hp with (rfl | rfl | rfl) <;> simp

    have hp' : p ∉ v.support := by
      intro hp'
      apply hp
      apply hv hp'

    simp at hp' hp
    push_neg at hp
    simp [hp', hp.1.symm, hp.2.1.symm, hp.2.2.symm]

  -- The fact that $g$ is the left inverse of $f$ is immediate from the definitions of $f$ and $g$.
  have g_circ_f (p) : g (f p) = p := by simp [f, g]

  -- Let's show that $g$ maps $s$ to $t$ bijectively and compl
  suffices t.card = 36 from ?_
  · rw [←this, ←Set.ncard_coe_Finset]
    apply Set.ncard_congr (fun v _ ↦ g v)

    -- The fact that $g$ maps $s$ to $t$ is immediate from the definitions of $s$ and $t$.
    · intro v
      simp [s, g, t]
      intros
      split_ands <;> assumption

    -- Now, let's show that $g$ is injective on $s$. Let $v, w \in s$. Assume that $g(v) = g(w)$.
    -- By definition of $s$, the supports of $v$ and $w$ are subsets of $\{2, 3, 5\}$.
    · intro v w hv hw h
      simp [s] at hv hw
      -- Then, because $f$ is the left inverse of $g$ on the set of finitely supported functions
      -- with support a subset of $\{2, 3, 5\}$, we have $f(g(v)) = f(g(w))$. This implies $v = w$.
      replace h : f (g v) = f (g w) := by rw [h]
      simpa [f_circ_g hv.1, f_circ_g hw.1] using h

    -- Finally, let's show that $g$ is surjective on $t$. Let $(a, b, c) \in t$. We need to show that
    -- there exists $v \in s$ such that $g(v) = (a, b, c)$.
    · intro p hp
      -- Choosing $v$ to be $f (a, b, c)$.
      use (f p)

      -- Because $f$ is the left inverse of $g$, we have $g(f(p)) = p$. So, we only need to show that
      -- $f (a, b, c)$ is in $s$.
      simp [g_circ_f]

      -- By definition of $f$, the support of $f (a, b, c)$ is a subset of $\{2, 3, 5\}$.
      have : (f p).support ⊆ {2, 3, 5} := by
        dsimp [f]
        calc _ ⊆ (((fun₀ | 2 => p.1) + fun₀ | 3 => p.2.1)).support ∪ (fun₀ | 5 => p.2.2).support := by apply Finsupp.support_add
             _ ⊆ ({2, 3, 5} : Finset ℕ) := ?_

        calc _ ⊆ ((fun₀ | 2 => p.1).support ∪ (fun₀ | 3 => p.2.1).support) ∪ (fun₀ | 5 => p.2.2).support := by gcongr; apply Finsupp.support_add
             _ ⊆ ({2, 3, 5} : Finset ℕ) := ?_

        calc _ ⊆ ({2} ∪ {3}) ∪ {5} := ?_
             _ ⊆ ({2, 3, 5} : Finset ℕ) := by decide

        gcongr <;> apply Finsupp.support_single_subset

      -- The other conditions are true by assumptions about $(a, b, c)$.
      simp [s]
      refine ⟨this, ?_⟩
      simp [f, t] at hp ⊢
      simp [hp]

  decide