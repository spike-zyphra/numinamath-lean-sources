import Mathlib


/- A function $f$ from the set of positive integers $\mathbb{N}$ into itself is such that for all $m, n \in \mathbb{N}$ the number $(m ^ 2 + n) ^ 2$ is divisible by $f ^ 2 (m) + f (n)$. Prove that $f(n) = n$ for each $n \in \mathbb{N}$. -/
theorem N3
    (f : ℕ → ℕ)
    (h : ∀ m n : ℕ, (f m ^ 2 + f n) ∣ (m ^ 2 + n) ^ 2) :
    ∀ n : ℕ, f n = n := by

  -- aux lemma
  have l_1 (a b : ℕ) (hb : b ≠ 0) (h : a ∣ b) : a ≤ b := by
    zify at h
    zify
    apply Int.le_of_dvd (by omega) h

  -- For $m=n=1$ we obtain that $f(1)^{2}+f(1)$ divides $\left(1^{2}+1\right)^{2}=4$, from which we find that $f(1)=1$.
  have r_f1 : f 1 = 1 := by
    specialize h 1 1
    have hle := l_1 _ _ (by simp) h
    by_contra! h_contra
    rcases Nat.eq_zero_or_pos (f 1) with hf1 | hf1
    . simp [hf1] at h
    . have : f 1 ≥ 2 := by omega
      have : f 1 ^ 2 + f 1 > 4 := by
        apply lt_add_of_le_of_pos ?_ hf1
        rw [show 4 = 2 ^ 2 by norm_num]
        exact Nat.pow_le_pow_of_le_left this 2
      norm_num at hle
      linarith only [this, hle]

  -- Next, we show that $f(p-1)=p-1$ for each prime $p$.
  have r_fp : ∀ p : ℕ, p.Prime → f (p - 1) = p - 1 := by
    intro p hpp
    have h_one_le_p := Nat.Prime.one_le hpp
    have h_two_le_p := Nat.Prime.two_le hpp

    -- By the hypothesis for $m=1$ and $n=p-1, f(p-1)+1$ divides $p^{2}$,
    have h' := h 1 (p - 1)
    rw [r_f1, one_pow, Nat.add_sub_cancel' h_one_le_p] at h'

    -- so $f(p-1)$ equals either $p-1$ or $p^{2}-1$.
    have : f (p - 1) = p - 1 ∨ f (p - 1) = p ^ 2 - 1 := by
      have ⟨k, ⟨hklt, hk⟩⟩ := (Nat.dvd_prime_pow hpp).mp h'
      interval_cases k
      . simp at hk
        specialize h (p - 1) (p - 1)
        simp [hk, zero_dvd_iff, show p - 1 ≠ 0 by omega] at h
      . left
        rw [pow_one] at hk
        omega
      . right
        omega

    -- If $f(p-1)=p^{2}-1$, then $f(1)+f(p-1)^{2}=p^{4}-2 p^{2}+2$ divides $\left(1+(p-1)^{2}\right)^{2} < p^{4}-2 p^{2}+2$, giving a contradiction. Hence $f(p-1)=p-1$.
    rcases this with hpv | hpv
    . exact hpv
    . specialize h (p - 1) 1
      zify at h
      rw [hpv, r_f1, Nat.cast_sub (Nat.one_le_pow 2 p h_one_le_p), Nat.cast_pow, Nat.cast_sub h_one_le_p, Nat.cast_one] at h
      set q : ℤ := (p : ℤ)
      apply Int.le_of_dvd (sq_pos_of_ne_zero (by linarith only [sq_nonneg (q - 1)])) at h
      have : (q ^ 2 - 1) ^ 2 + 1 > ((q - 1) ^ 2 + 1) ^ 2 := by
        apply Int.lt_of_sub_pos
        rw [show (q ^ 2 - 1) ^ 2 + 1 - ((q - 1) ^ 2 + 1) ^ 2 = 2 * (q - 1) ^ 2 * (2 * q - 1) by ring_nf]
        repeat apply mul_pos
        . linarith only
        . exact pow_pos (by linarith only [h_two_le_p]) _
        . linarith only [h_one_le_p]
      linarith only [this, h]

  -- Let us now consider an arbitrary $n \in \mathbb{N}$.
  intro n
  have r_dvd : ∀ p : ℕ, p.Prime → (f n + (p - 1) ^ 2 : ℤ) ∣ (n - f n) ^ 2 := by
    intro p hpp
    -- By the hypothesis for $m=p-1$, $A=f(n)+(p-1)^{2}$ divides $\left(n+(p-1)^{2}\right)^{2} \equiv(n-f(n))^{2}(\bmod A)$, and hence $A$ divides $(n-f(n))^{2}$ for any prime $p$.
    specialize h (p - 1) n
    rw [r_fp p hpp] at h
    zify at h
    rw [Nat.cast_sub (Nat.Prime.one_le hpp), Nat.cast_one] at h
    apply Int.dvd_of_emod_eq_zero
    have : (n - f n : ℤ) ^ 2 % (f n + (p - 1) ^ 2) = ((p - 1) ^ 2 + n) ^ 2 % (f n + (p - 1) ^ 2) := by
      apply Int.ModEq.pow
      calc (n : ℤ) - f n
        _ ≡ n - f n + (f n + (p - 1) ^ 2) [ZMOD (f n + (p - 1) ^ 2)] := by
          exact Int.ModEq.symm Int.add_modEq_right
      rw [← add_assoc, sub_add_cancel, add_comm (n : ℤ)]
    rw [this, add_comm (f n : ℤ), EuclideanDomain.mod_eq_zero]
    convert h

  -- Taking $p$ large enough, we can obtain $A$ to be greater than $(n-f(n))^{2}$
  have : ∃ p : ℕ, f n + (p - 1) ^ 2 > ((n : ℤ) - f n) ^ 2 ∧ p.Prime := by
    set t : ℤ := ((n : ℤ) - f n) ^ 2 + 3
    have : (t - 1) ^ 2 > t - 1 := by
      refine lt_self_pow ?_ Nat.one_lt_two
      dsimp [t]
      rw [add_sub_assoc, show (3 : ℤ) - 1 = 1 + 1 by norm_num, ← add_assoc]
      refine Int.lt_add_of_le_of_pos ?_ ?_
      . exact Int.le_add_of_nonneg_left (sq_nonneg _)
      . exact Int.zero_lt_one
    obtain ⟨p, ⟨hp, hpp⟩⟩ := Nat.exists_infinite_primes (t.toNat + 5)

    have t1 : p - 1 ≤ (p - 1) ^ 2 := Nat.le_self_pow (by linarith only) (p - 1)
    zify at t1
    rw [Nat.cast_sub (Nat.one_le_of_lt hp), Nat.cast_one] at t1

    use p
    constructor
    . calc (f n : ℤ) + (p - 1) ^ 2
        _ ≥ p - 1 := by
          linarith only [t1]
        _ > (n - f n) ^ 2 := by
          zify at hp
          have : t.toNat = t := by
            refine Int.toNat_of_nonneg ?_
            dsimp [t]
            apply add_nonneg (sq_nonneg _) (by linarith only)
          simp only [this, t] at hp
          linarith only [hp]
    . exact hpp
  obtain ⟨p, ⟨hp, hpp⟩⟩ := this

  -- which implies that $(n-f(n))^{2}=0$, i.e., $f(n)=n$ for every $n$​.
  specialize r_dvd p hpp
  have : ((n : ℤ) - f n) ^ 2 = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (sq_nonneg _) hp r_dvd
  apply pow_eq_zero at this
  linarith only [this]

