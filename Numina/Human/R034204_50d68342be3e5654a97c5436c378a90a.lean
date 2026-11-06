import Mathlib

/- Let $\mathbb{P}$ be the set of all prime numbers. Find all functions $f: \mathbb{P} \rightarrow \mathbb{P}$ such that

$$
f(p)^{f(q)}+q^{p}=f(q)^{f(p)}+p^{q}
$$

holds for all $p, q \in \mathbb{P}$.
Proposed by Albania -/
theorem number_theory_604604 (f : ℕ → ℕ) (fmapsto : f '' {p | p.Prime} ⊆ {p | p.Prime}) :
(∀ p q, p.Prime → q.Prime → f p ^ f q + q ^ p = f q ^ f p + p ^ q) ↔ ∀ p, p.Prime → f p = p := by
  simp [Set.subset_def] at fmapsto
  constructor
-- Assuming the functional equation, we first prove that $f(2)=2$
  · intro heq; have f2 : f 2 = 2 := by
    -- Assume the contrary that $f(2)$ is not $2$, then it must be an odd prime
      by_contra! h; have f2par : Odd (f 2) := by
        apply Nat.Prime.odd_of_ne_two; apply fmapsto; norm_num; exact h
    -- Prove that $f$ maps any odd prime to $2$ by parity reasons
      have fodd : ∀ p, p.Prime → p ≠ 2 → f p = 2 := by
        specialize heq 2; intro p ppr pne; specialize heq p Nat.prime_two ppr
        specialize fmapsto p ppr; rcases fmapsto.eq_two_or_odd' with _|fppar; assumption
        have : Odd (f p ^ f 2 + 2 ^ p) := by
          apply Odd.add_even; apply Odd.pow; exact fppar
          rw [Nat.even_pow]; simp; have := ppr.two_le; linarith
        rw [← Nat.not_even_iff_odd] at this; suffices : Even (f p ^ f 2 + 2 ^ p); contradiction
        rw [← heq]; apply Odd.add_odd; apply Odd.pow; exact f2par
        apply Odd.pow; apply ppr.odd_of_ne_two; exact pne
    -- Take two distinct odd primes $p$ and $q$, specialize heq to $p$ and $q$
      obtain ⟨p, ⟨_,ppr⟩⟩ := Nat.exists_infinite_primes 3; obtain ⟨q, ⟨_,qpr⟩⟩ := Nat.exists_infinite_primes (p+1)
      have podd : Odd p := by apply ppr.odd_of_ne_two; linarith
      have qodd : Odd q := by apply qpr.odd_of_ne_two; linarith
    -- Plug in $f(p)=2$ and $f(q)=2$ to heq
      specialize heq p q ppr qpr; repeat rw [fodd] at heq
    -- Prove $p=q$, which is a contradiction
      simp at heq; have : q ∣ p ^ q := by
        rw [← heq]; use q ^ (p - 1); rw [← pow_succ', Nat.sub_add_cancel]; linarith
      apply Nat.prime_eq_prime_of_dvd_pow at this; linarith; any_goals assumption
      all_goals linarith
  -- Define $g(n)$ to be the function $2^n-n^2$
    let g : ℕ → ℤ := fun n => 2 ^ n - n ^ 2
  -- Prove that $g$ is strictly increasing when $n>2$
    have gmono : StrictMonoOn g (Set.Ioi 2) := by
      apply strictMonoOn_of_lt_add_one; exact Set.ordConnected_Ioi; simp
      intro n ngt _; simp [g, pow_succ, mul_two, ← sub_pos]; ring_nf
      rw [neg_sub_left, ← sub_eq_neg_add, sub_pos]; norm_cast
      rw [Nat.lt_iff_add_one_le, add_assoc, ← mul_two, ← Nat.add_mul]
      nth_rw 2 [show n = n-1+1 by rw [Nat.sub_add_cancel]; linarith]
      rw [pow_succ]; apply Nat.mul_le_mul_right
      have := @Nat.lt_pow_self (n-2) 2 (show _ by simp)
      rw [Nat.sub_lt_iff_lt_add, Nat.lt_iff_add_one_le] at this
      apply Nat.le_trans this; rw [show n-1 = n-2+1 by zify; rw [Nat.cast_sub, Nat.cast_sub]; ring; all_goals linarith]
      simp [pow_succ, mul_two]; apply Nat.le_self_pow
      intro h; rw [Nat.sub_eq_zero_iff_le] at h; all_goals linarith
  -- Take any prime number $p$, if $p=2$ then we already have $f(2)=2$
    intro p ppr; by_cases hp : p ≤ 2
    · replace hp : p = 2 := by have := ppr.two_le; linarith
      rw [hp, f2]
  -- If $p$ is greater than $2$, specialize heq at $p$, $2$ and rearrange its terms
  -- we can apply the monotonicity of $g$ to prove the final goal
    specialize heq p 2 ppr Nat.prime_two; rw [f2] at heq; zify at heq
    rw [add_comm, ← sub_eq_sub_iff_add_eq_add] at heq; rw [← gmono.eq_iff_eq]
    simp [g]; symm; exact heq
    · simp; by_contra h; replace h : f p = 2 := by have := (fmapsto p ppr).two_le; linarith
      simp [h] at heq; rw [sub_eq_zero] at heq; norm_cast at heq
      have : p ∣ 2 ^ p := by use p; rw [← pow_two]; exact heq
      apply Nat.prime_eq_prime_of_dvd_pow at this; linarith; exact ppr; exact Nat.prime_two
    simp; linarith
-- Conversely, it is straightforward to check that the functional equation holds if $f(p)=p$ for all primes
  intro hf p q ppr qpr; repeat rw [hf]
  ring; all_goals assumption