import Mathlib
set_option maxHeartbeats 500000

--Show that 35 divides 27^(2 * k + 1) + 8^(2 * k + 1) for all k.
lemma help1 (k : ℕ) : 35 ∣ 27^(2 * k + 1) + 8^(2 * k + 1) := by
    induction' k with k hk
    simp
    have h1 : 27 ^ (2 * (k + 1) + 1) + 8 ^ (2 * (k + 1) + 1) = 27 ^ (2 * k + 1) * 27 ^ 2 + 8 ^ (2 * k + 1) * 8 ^ 2 := by
        ring_nf
    rw [h1]
    omega

--Show that 35 divides 729^k - 64^k for all k.
lemma help2 (k : ℕ) : 35 ∣ 729^k - 64^k := by
    have h1 : 729 ^ k % 5 = 4 ^ k % 5 := by
        have h1 : ∀ k : ℕ, 729 ^ k % 5 = 4 ^ k % 5 := by
            intro k
            induction k with
            | zero =>
                simp
            | succ k ih =>
                simp [Nat.pow_succ, Nat.mul_mod, ih]

        specialize h1 k
        exact h1
    have h2 : 64 ^ k % 5 = 4 ^ k % 5 := by
        have h2 : ∀ k : ℕ, 64 ^ k % 5 = 4 ^ k % 5 := by
            intro k
            induction k with
            | zero =>
                simp
            | succ k ih =>
                simp [Nat.pow_succ, Nat.mul_mod, ih]

        specialize h2 k
        exact h2
    have hk1 : (729 ^ k - 64 ^ k) % 5 = 0 := by
        omega
    -- For modulus 7
    have h3 : 729 ^ k % 7 = 1 ^ k % 7 := by
        have h1 : ∀ k : ℕ, 729 ^ k % 7 = 1 ^ k % 7 := by
            intro k
            induction k with
            | zero =>
                simp
            | succ k ih =>
                simp [Nat.pow_succ, Nat.mul_mod, ih]

        specialize h1 k
        exact h1
    have h4 : 64 ^ k % 7 = 1 ^ k % 7 := by
        have h2 : ∀ k : ℕ, 64 ^ k % 7 = 1 ^ k % 7 := by
            intro k
            induction k with
            | zero =>
                simp
            | succ k ih =>
                simp [Nat.pow_succ, Nat.mul_mod, ih]

        specialize h2 k
        exact h2
    have hk2 : (729 ^ k - 64 ^ k) % 7 = 0 := by
        omega
    -- Now we can conclude that 35 divides (729^k - 64^k) since it is divisible by both 5 and 7 which are coprime
    omega

/- 2. Prove that for every natural number $n$ at least one of the numbers $3^{3 n}+2^{3 n}$ and $3^{3 n}-2^{3 n}$ is divisible by 35. -/
theorem number_theory_246699 (n : ℕ) :
    35 ∣ (3^(3*n) + 2^(3*n)) ∨ 35 ∣ (3^(3*n) - 2^(3*n)) := by
        --n is either odd or even.
        have H1 : Odd n ∨ Even n := by exact Or.symm (Nat.even_or_odd n)
        rcases H1 with H2|H2
        --n is odd.
        obtain ⟨k,hk⟩ := H2
        rw [hk]
        left
        have : 3 ^ (3 * (2 * k + 1)) + 2 ^ (3 * (2 * k + 1)) = 27^(2 * k + 1) + 8^(2 * k + 1) := by
            rw [Nat.pow_mul, Nat.pow_mul]
        rw [this]
        apply help1
        --n is even.
        obtain ⟨k,hk⟩ := H2
        right
        rw [show k + k = 2 * k by omega] at hk
        rw [hk]
        have : 3 ^ (3 * (2 * k)) - 2 ^ (3 * (2 * k)) = 729^k - 64^k := by
            rw [Nat.pow_mul, Nat.pow_mul, Nat.pow_mul, Nat.pow_mul]
        rw [this]
        apply help2