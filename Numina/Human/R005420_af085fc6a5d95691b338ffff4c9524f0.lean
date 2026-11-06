import Mathlib

/-
Evaluate the functions $\phi(n), \sigma(n)$, and $\tau(n)$ for $n=12, n=2007$, and $n=2^{2007}$.
-/

theorem number_theory_606032 : Nat.totient 12 = 4  ∧  (∑ d ∈ (Nat.divisors 12), d) = 28 ∧ (Nat.divisors 12).card = 6 ∧ Nat.totient 2007 = 1332  ∧  (∑ d ∈ (Nat.divisors 2007), d) = 2912 ∧ (Nat.divisors 2007).card = 6 ∧ Nat.totient (2^2007) = 2^2006  ∧  (∑ d ∈ (Nat.divisors (2^2007)), d) = 2^2008-1 ∧ (Nat.divisors (2^2007)).card = 2008 := by
    constructor
    native_decide
    constructor
    native_decide
    constructor
    native_decide

    constructor
    native_decide
    constructor
    native_decide
    constructor
    native_decide

    have prim2: Nat.Prime 2 := by norm_num
    have tmp1: ∀ t : ℕ, (2^(t+1)).totient = 2^t := by
      intro t
      have :  (2 ^ (t + 1)).totient = 2 ^ t * (2 - 1) := by apply Nat.totient_prime_pow_succ prim2 t
      ring_nf at this
      assumption
    have tmp2: ∀ t : ℕ, ∑ d ∈ (2 ^ (t+1)).divisors, d = 2 ^ (t+2) - 1 := by
      intro t
      induction' t with n hn
      simp; norm_num
      simp_all; 
      have : ∑ x ∈ Finset.range (n + 1 + 1 + 1), 2 ^ x = ∑ x ∈ Finset.range (n + 1 + 1 ), 2 ^ x + 2^(n+2) := by 
        exact Finset.sum_range_succ (HPow.hPow 2) (n + 2)
      rw [this]; rw [hn]; 
      have : 1 ≤ 2^(n) := by exact Nat.one_le_two_pow
      have : 4 ≤ 2 ^ n * 4 := by nlinarith
      have : 2 ^ n * 8 = 2^n * 4 + 2^n * 4:= by ring_nf
      ring_nf; rw [this]; 
      let N := 2^n * 4
      have : N - 1 + N = N + N - 1 := by 
        have : 4 ≤ N := by simp [N]; assumption
        ring_nf; omega
      assumption
        
    have tmp3: ∀ t : ℕ,  (2 ^ (t+1)).divisors.card = t + 2 := by
      intro t
      rw [Nat.card_divisors]
      have : 0 < 2^(t+1) := by exact Nat.two_pow_pos (t + 1)
      have : (2 ^ (t+1)).primeFactors = {2} := by 
        apply Nat.primeFactors_prime_pow
        linarith
        norm_num
      rw [this]; simp; norm_num
      positivity

    have : ∀ t : ℕ, (2^(t+1)).totient = 2^t ∧ ∑ d ∈ (2 ^ (t+1)).divisors, d = 2 ^ (t+2) - 1 ∧ (2 ^ (t+1)).divisors.card = t+2 := by
      intro t
      constructor; apply tmp1 t
      constructor; apply tmp2 t
      apply tmp3 t

    have tar: (2 ^ (2006+1)).totient = 2 ^ 2006 ∧ ∑ d ∈ (2 ^ (2006+1)).divisors, d = 2 ^ (2006+2) - 1 ∧ (2 ^ (2006+1)).divisors.card = 2006+2 := by exact this 2006

    have p1: 2006 + 1 = 2007 := by norm_num
    have p2: 2006 + 2 = 2008 := by norm_num
    rw [p1, p2] at tar; exact tar
