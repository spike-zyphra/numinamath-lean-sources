import Mathlib

/- Denote by $d(n)$ the number of distinct positive divisors of a positive integer $n$ (including 1 and $n$ ). Let $a>1$ and $n>0$ be integers such that $a^{n}+1$ is a prime. Prove that

$$
d\left(a^{n}-1\right) \geq n .
$$ -/
theorem number_theory_604802 (a n : ℕ) (ha : a > 1) (hn : n > 0) (hprime : Nat.Prime (a ^ n + 1)) :
  (Nat.divisors (a ^ n - 1)).card ≥ n := by
  -- First, we show that n must be a power of 2
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 ^ k := by
    -- We have a lemma that says that one of the following must be true:
    -- 1. n is a power of 2
    -- 2. n has an odd prime factor
    obtain h | ⟨p, hp, ⟨m, rfl⟩, hpodd⟩ := Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
    -- If n is a power of 2, then we're done.
    . exact h
    -- If n has an odd prime factor, then a^n + 1 = (a^m)^p + 1, which is divisible by a^m + 1.
    . absurd hprime
      apply Nat.not_prime_of_dvd_of_lt (m := a ^ m + 1)
      . rw [show a ^ (p * m) + 1 = (a ^ m) ^ p + 1 ^ p by rw [mul_comm, pow_mul, one_pow]]
        exact Odd.nat_add_dvd_pow_add_pow _ _ hpodd
      -- We still need to show that 1 < a^m + 1 < a^n + 1.
      . simp
        exact Nat.one_le_pow m a (Nat.zero_lt_of_lt ha)
      . suffices H : m < p * m from Nat.add_lt_add_right ((Nat.pow_lt_pow_iff_right ha).mpr H) _
        exact (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_mul_pos_left hn)).mpr (Nat.Prime.one_lt hp)
  -- Now we forget the primality condition and prove the result by induction.
  clear hn hprime
  induction k with
  | zero =>
    -- Base case
    simp
    exact Nat.sub_ne_zero_iff_lt.mpr ha
  | succ k ih =>
    -- Inductive step, if a^2^k - 1 has at least 2^k divisors, we need to show that a^2^(k+1) - 1 has at least 2^(k+1) divisors.
    -- a^2^(k+1) - 1 = (a^2^k + 1)(a^2^k - 1)
    -- So the divisors of a^2^(k+1) - 1 contain the divisors of a^2^k - 1 and (a^2^k + 1) times the divisors of a^2^k - 1.
    have H₁ : (a ^ 2 ^ k - 1).divisors ∪ (a ^ 2 ^ k - 1).divisors.map {toFun := fun x ↦ (a ^ 2 ^ k + 1) * x, inj' := fun x y ↦ by simp} ⊆
      (a ^ 2 ^ (k + 1) - 1).divisors := by
      intro x hx
      have h₀ : a ^ 2 ^ (k + 1) - 1 = (a ^ 2 ^ k + 1) * (a ^ 2 ^ k - 1) := by
        rw [pow_succ, pow_mul]
        exact Nat.sq_sub_sq _ 1
      rw [h₀]
      clear h₀
      simp only [Finset.mem_union, Finset.mem_map] at hx
      rcases hx with hx | hx
      . simp at hx ⊢
        exact ⟨Dvd.dvd.mul_left hx.1 _, hx.2⟩
      . rcases hx with ⟨d, hd, rfl⟩
        simp at hd
        simp
        exact ⟨Nat.mul_dvd_mul_left _ hd.1, hd.2⟩
    calc
      _ ≥ ((a ^ 2 ^ k - 1).divisors ∪ (a ^ 2 ^ k - 1).divisors.map {toFun := fun x ↦ (a ^ 2 ^ k + 1) * x, inj' := fun x y ↦ by simp}).card := Finset.card_le_card H₁
      -- The two sets are disjoint, so we can just add the sizes of the two sets.
      _ = (a ^ 2 ^ k - 1).divisors.card + ((a ^ 2 ^ k - 1).divisors.map {toFun := fun x ↦ (a ^ 2 ^ k + 1) * x, inj' := fun x y ↦ by simp}).card := by
        -- Every member of the first set ≤ a^2^k - 1, and every member of the second set ≥ a^2^k + 1.
        refine Finset.card_union_of_disjoint (Finset.disjoint_iff_ne.mpr ?_)
        rintro x hx y hy rfl
        simp at hy
        rcases hy with ⟨z, -, rfl⟩
        obtain ⟨h₁, h₂⟩ := Nat.mem_divisors.mp hx
        replace h₁ : a ^ 2 ^ k + 1 ≤ a ^ 2 ^ k - 1 := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h₂) (dvd_of_mul_right_dvd h₁)
        absurd h₁
        simp
        exact Nat.sub_lt_succ (a ^ 2 ^ k) 1
      _ = (a ^ 2 ^ k - 1).divisors.card + (a ^ 2 ^ k - 1).divisors.card := by
        congr 1
        exact Finset.card_map _
      _ ≥ 2 ^ k + 2 ^ k := Nat.add_le_add ih ih
      _ = 2 ^ (k + 1) := by ring
