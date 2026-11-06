import Mathlib

/- Denote by $d(n)$ the number of all positive divisors of a positive integer $n$ (including 1 and $n$ ).
Prove that there are infinitely many $n$ such that $\frac{n}{d(n)}$ is an integer. -/
theorem number_theory_605940 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ n.divisors.card ∣ n := by

    -- we will construct the answer n = p ^ (p - 1) --
    intro N
    have Exist_p: ∃ p: ℕ, N + 1 ≤ p ∧ Nat.Prime p := by
        apply Nat.exists_infinite_primes
    obtain ⟨p,hp⟩ := Exist_p
    rcases hp with ⟨bp,prime_p⟩
    have bp2: 2 ≤ p := by
            by_contra! bp2
            have h1: p = 0 ∨ p = 1 := by
                omega
            rcases h1 with h | h
            .   rw [h] at prime_p
                omega
            .   rw [h] at prime_p
                absurd prime_p
                norm_num
    let n:= p ^ (p - 1)
    use n
    constructor
    .   simp [n]
        calc
            N < N + 1 := by omega
            _ ≤ p := by omega
            _ ≤ p ^ (p - 1) := by nth_rewrite 1[show p = p ^ 1 by ring]; apply Nat.pow_le_pow_of_le_right;omega;omega
    .   simp [n]
        -- it's a little bit tricky to prove this, where we used the finset.map to handle --
        have count_divisor: (p ^ (p - 1)).divisors.card = p := by
            have div_seq: (p ^ (p - 1)).divisors = Finset.map { toFun := fun x => p ^ x, inj' := by apply pow_right_injective₀;omega;omega} (Finset.range p) := by
                rw [Nat.divisors_prime_pow]
                simp
                rw [show p- 1 + 1 = p by apply Nat.sub_add_cancel;omega]
                exact prime_p
            rw [div_seq]
            simp
        rw [count_divisor]
        apply dvd_pow_self
        omega