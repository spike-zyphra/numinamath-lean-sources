import Mathlib
/- Let $N$ be a positive integer. Let $S_N = \sum_{k=1}^{N} 2022^{2022^k}$. We want to find the value of $S_N \pmod{100}$.-/
theorem number_theory_638133 (n S : ℕ) (hn : n > 0) (h : S = ∑ i in Finset.range n, 2022 ^ (2022 ^ (i + 1))) : (n ≡ 1 [MOD 4] → S ≡ 84 + 4 * ((n - 1) / 4) [MOD 100]) ∧ (n ≡ 2 [MOD 4] → S ≡ 40 + 4 * ((n - 1) / 4) [MOD 100]) ∧ (n ≡ 3 [MOD 4] → S ≡ 76 + 4 * ((n - 1) / 4) [MOD 100]) ∧ (n ≡ 0 [MOD 4] → S ≡ 72 + 4 * ((n - 1) / 4) [MOD 100]):= by
  -- Set m = n - 1 and clear its value for later use
  set m:= n - 1 with hm
  clear_value m
  -- Replace the hypothesis to express n in terms of m
  replace hm : n = m + 1:= by omega
  subst n
  clear hn
  -- Express m in terms of its quotient and remainder when divided by 4
  have h1 : m = 4 * (m / 4) + m % 4:= by exact Eq.symm (Nat.div_add_mod m 4)

  -- Key lemma: 2022^(2022^k) ≡ 22^(2^k) [MOD 100] for all k
  have h2 : ∀ k : ℕ, 2022 ^ (2022 ^ k) ≡ 22 ^ (2 ^ k) [MOD 100]:= by
    intro k
    by_cases hkpos : k = 0
    .
      -- Base case: k = 0
      subst k
      simp
      rfl
    .
      -- Case: k > 0, need to prove 2022^(2022^k) ≡ 22^(2^k) [MOD 100]
      have g1 : 2022 ≡ 22 [MOD 100]:= by rfl
      replace g1 : 2022 ^ (2 ^ k) ≡ 22 ^ (2 ^ k) [MOD 100]:= by exact Nat.ModEq.pow (2 ^ k) g1
      suffices 2022 ^ (2022 ^ k) ≡ 2022 ^ (2 ^ k) [MOD 100] by exact Nat.ModEq.trans this g1

      -- Show that 2022^k ≡ 2^k [MOD 20]
      have g2 : 2022 ≡ 2 [MOD 20]:= by rfl
      replace g2 : 2022 ^ k ≡ 2 ^ k [MOD 20]:= by exact Nat.ModEq.pow k g2
      have g3 : 2022 ^ k ≥ 2 ^ k:= by
        have g4 : 2022 ≥ 2:= by omega
        exact Nat.pow_le_pow_of_le_left g4 k
      replace g2 : 20 ∣ 2022 ^ k - 2 ^ k:= by exact (Nat.modEq_iff_dvd' g3).mp (id (Nat.ModEq.symm g2))
      rcases g2 with ⟨t, ht⟩
      replace ht : 2022 ^ k = 20 * t + 2 ^ k:= by omega
      rw [ht]
      ring_nf
      rw [show t * 20 = 20 * t by omega]

      -- Use the fact that 22^20 ≡ 76 [MOD 100] and its powers
      have g4 : 2022 ≡ 22 [MOD 100]:= by rfl
      replace g4:= Nat.ModEq.pow (20 * t) g4
      rw [show 22 ^ (20 * t) = (22 ^ 20) ^ t by exact Nat.pow_mul 22 20 t] at g4
      have g5 : 22 ^ 20 ≡ 76 [MOD 100]:= by rfl
      replace g5 : ∀ k : ℕ, (22 ^ 20) ^ (k + 1) ≡ 76 [MOD 100]:= by
        intro k
        induction k with
        | zero =>
          simp
          exact g5
        | succ k ih =>
          rw [show (22 ^ 20) ^ (k + 1 + 1) = (22 ^ 20) ^ (k + 1) * 22 ^ 20 by ring]
          set a:= 22 ^ 20 with ha
          clear_value a
          exact Nat.ModEq.mul ih g5

      -- Show that t > 0 (since 2022^k > 2^k for k > 0)
      have htpos : t > 0:= by
        by_contra H
        simp at H
        subst t
        simp at ht
        have g5 : 2022 > 2:= by omega
        replace g5 : 2022 ^ k > 2 ^ k:= by exact Nat.pow_lt_pow_left g5 hkpos
        linarith
      specialize g5 (t - 1)
      rw [show t - 1 + 1 = t by omega] at g5
      replace g4 : 2022 ^ (20 * t) ≡ 76 [MOD 100]:= by exact Nat.ModEq.trans g4 g5
      replace g4 : 2022 ^ (20 * t) * 2022 ^ (2 ^ k) ≡ 76 * 2022 ^ (2 ^ k) [MOD 100]:= by exact Nat.ModEq.mul g4 rfl
      suffices 76 * 2022 ^ (2 ^ k) ≡ 2022 ^ (2 ^ k) [MOD 100] by exact Nat.ModEq.trans g4 this

      -- Prove that 76 * 2022^(2*(n+1)) ≡ 2022^(2*(n+1)) [MOD 100] for all n
      have g6 : ∀ n : ℕ, 76 * 2022 ^ (2 * (n + 1)) ≡ 2022 ^ (2 * (n + 1)) [MOD 100]:= by
        intro n
        induction n with
        | zero =>
          simp
          rfl
        | succ n ih =>
          rw [show 2 * (n + 1 + 1) = 2 + 2 * (n + 1) by ring_nf]
          rw [show 2022 ^ (2 + 2 * (n + 1)) = 2022 ^ 2 * 2022 ^ (2 * (n + 1)) by ring_nf]
          rw [show 76 * (2022 ^ 2 * 2022 ^ (2 * (n + 1))) = 76 * 2022 ^ 2 * 2022 ^ (2 * (n + 1)) by ring]
          set a:= 2022 ^ (2 * (n + 1))
          clear_value a
          have g : 76 * 2022 ^ 2 ≡ 2022 ^ 2 [MOD 100]:= by rfl
          exact Nat.ModEq.mul g rfl
      specialize g6 (2 ^ (k - 1) - 1)
      have g : 2 ^ (k - 1) > 0:= by positivity
      rw [show 2 ^ (k - 1) - 1 + 1 = 2 ^ (k - 1) by omega] at g6
      rw [show 2 * 2 ^ (k - 1) = 2 ^ (k - 1 + 1) by ring_nf] at g6
      rw [show k - 1 + 1 = k by omega] at g6
      exact g6

  -- Lemma: 22^(2^(t+6)) ≡ 22^(2^(t+2)) [MOD 100] for all t (periodicity)
  have h3 : ∀ t : ℕ, 22 ^ (2 ^ (t + 6)) ≡ 22 ^ (2 ^ (t + 2)) [MOD 100]:= by
    intro t
    induction t with
    | zero =>
      simp
      rfl
    | succ t ih =>
      replace ih:= Nat.ModEq.mul ih ih
      rw [show 22 ^ 2 ^ (t + 6) * 22 ^ 2 ^ (t + 6) = 22 ^ (2 * 2 ^ (t + 6)) by ring_nf] at ih
      rw [show 2 * 2 ^ (t + 6) = 2 ^ (t + 1 + 6) by ring_nf] at ih
      rw [show 22 ^ 2 ^ (t + 2) * 22 ^ 2 ^ (t + 2) = 22 ^ (2 * 2 ^ (t + 2)) by ring_nf] at ih
      rw [show 2 * 2 ^ (t + 2) = 2 ^ (t + 1 + 2) by ring_nf] at ih
      exact ih

  -- Calculate specific values for different congruence classes modulo 4
  -- For k ≡ 2 [MOD 4]: 22^(2^(4k+2)) ≡ 56 [MOD 100]
  have h4 : ∀ k : ℕ, 22 ^ (2 ^ (4 * k + 2)) ≡ 56 [MOD 100]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 4 * (k + 1) + 2 = 4 * k + 6 by ring]
      specialize h3 (4 * k)
      exact Nat.ModEq.trans h3 ih

  -- For k ≡ 3 [MOD 4]: 22^(2^(4k+3)) ≡ 36 [MOD 100]
  have h5 : ∀ k : ℕ, 22 ^ (2 ^ (4 * k + 3)) ≡ 36 [MOD 100]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 4 * (k + 1) + 3 = 4 * k + 1 + 6 by ring]
      rw [show 4 * k + 3 = 4 * k + 1 + 2 by ring] at ih
      specialize h3 (4 * k + 1)
      exact Nat.ModEq.trans h3 ih

  -- For k ≡ 0 [MOD 4]: 22^(2^(4k+4)) ≡ 96 [MOD 100]
  have h6 : ∀ k : ℕ, 22 ^ (2 ^ (4 * k + 4)) ≡ 96 [MOD 100]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 4 * (k + 1) + 4 = 4 * k + 2 + 6 by ring]
      rw [show 4 * k + 4 = 4 * k + 2 + 2 by ring] at ih
      specialize h3 (4 * k + 2)
      exact Nat.ModEq.trans h3 ih

  -- For k ≡ 1 [MOD 4]: 22^(2^(4k+5)) ≡ 16 [MOD 100]
  have h7 : ∀ k : ℕ, 22 ^ (2 ^ (4 * k + 5)) ≡ 16 [MOD 100]:= by
    intro k
    induction k with
    | zero =>
      simp
      rfl
    | succ k ih =>
      rw [show 4 * (k + 1) + 5 = 4 * k + 3 + 6 by ring]
      rw [show 4 * k + 5 = 4 * k + 3 + 2 by ring] at ih
      specialize h3 (4 * k + 3)
      exact Nat.ModEq.trans h3 ih

  -- Main lemma: The sum can be reduced modulo 100 using h2
  have h8 : ∀ n : ℕ, ∑ i ∈ Finset.range n, 2022 ^ 2022 ^ (i + 1) ≡ ∑ i ∈ Finset.range n, 22 ^ 2 ^ (i + 1) [MOD 100]:= by
    intro n
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      specialize h2 (n + 1)
      exact Nat.ModEq.add ih h2
  specialize h8 (m + 1)
  rw [←h] at h8
  set n:= m / 4
  clear_value n

  -- Prove the four cases based on the remainder of n modulo 4
  refine ⟨?_, ?_, ?_, ?_⟩
  .
    -- Case 1: n ≡ 1 [MOD 4] implies S ≡ 84 + 4*((n-1)/4) [MOD 100]
    intro g
    replace g : m ≡ 0 [MOD 4]:= by
      suffices m + 1 ≡ 0 + 1 [MOD 4] by exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 1 (id (Nat.ModEq.symm this)))
      simp
      exact g
    rw [g] at h1
    simp at h1
    clear g
    subst m
    suffices ∑ i ∈ Finset.range (4 * n + 1), 22 ^ 2 ^ (i + 1) ≡ 84 + 4 * n [MOD 100] by exact Nat.ModEq.trans h8 this
    clear h h8
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [show 4 * (n + 1) + 1 = 4 * n + 5 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 4 * n + 4 + 1 = 4 * n + 5 by omega]
      rw [show 4 * n + 3 + 1 = 4 * n + 4 by omega]
      rw [show 4 * n + 2 + 1 = 4 * n + 3 by omega]
      rw [show 4 * n + 1 + 1 = 4 * n + 2 by omega]
      replace h4:= h4 n
      replace h5:= h5 n
      replace h6:= h6 n
      replace h7:= h7 n
      replace ih:= Nat.ModEq.add ih h4
      replace ih:= Nat.ModEq.add ih h5
      replace ih:= Nat.ModEq.add ih h6
      replace ih:= Nat.ModEq.add ih h7
      have g1 : 84 + 4 * n + 56 + 36 + 96 + 16 ≡ 84 + 4 * (n + 1) [MOD 100]:= by
        rw [show 84 + 4 * (n + 1) = 84 + 4 * (n + 1) + 0 by ring]
        rw [show 84 + 4 * n + 56 + 36 + 96 + 16 = 84 + 4 * (n + 1) + 200 by ring]
        have g2 : 200 ≡ 0 [MOD 100]:= by rfl
        exact Nat.ModEq.add rfl g2
      exact Nat.ModEq.trans ih g1
  .
    -- Case 2: n ≡ 2 [MOD 4] implies S ≡ 40 + 4*((n-1)/4) [MOD 100]
    intro g
    replace g : m ≡ 1 [MOD 4]:= by
      suffices m + 1 ≡ 1 + 1 [MOD 4] by exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 1 (id (Nat.ModEq.symm this)))
      simp
      exact g
    rw [g] at h1
    simp at h1
    clear g
    subst m
    suffices ∑ i ∈ Finset.range (4 * n + 1 + 1), 22 ^ 2 ^ (i + 1) ≡ 40 + 4 * n [MOD 100] by exact Nat.ModEq.trans h8 this
    clear h h8
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [show 4 * (n + 1) + 1 = 4 * n + 5 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 4 * n + 4 + 1 = 4 * n + 5 by omega]
      rw [show 4 * n + 3 + 1 = 4 * n + 4 by omega]
      rw [show 4 * n + 2 + 1 = 4 * n + 3 by omega]
      rw [show 4 * n + 5 + 1 = 4 * (n + 1) + 2 by omega]
      replace h4:= h4 (n + 1)
      replace h5:= h5 n
      replace h6:= h6 n
      replace h7:= h7 n
      replace ih:= Nat.ModEq.add ih h5
      replace ih:= Nat.ModEq.add ih h6
      replace ih:= Nat.ModEq.add ih h7
      replace ih:= Nat.ModEq.add ih h4
      have g1 : 40 + 4 * n + 36 + 96 + 16 + 56 ≡ 40 + 4 * (n + 1) [MOD 100]:= by
        rw [show 40 + 4 * (n + 1) = 40 + 4 * (n + 1) + 0 by ring]
        rw [show 40 + 4 * n + 36 + 96 + 16 + 56 = 40 + 4 * (n + 1) + 200 by ring]
        have g2 : 200 ≡ 0 [MOD 100]:= by rfl
        exact Nat.ModEq.add rfl g2
      rw [show 4 * n + 1 + 1 = 4 * n + 2 by omega] at ih
      exact Nat.ModEq.trans ih g1
  .
    -- Case 3: n ≡ 3 [MOD 4] implies S ≡ 76 + 4*((n-1)/4) [MOD 100]
    intro g
    replace g : m ≡ 2 [MOD 4]:= by
      suffices m + 1 ≡ 2 + 1 [MOD 4] by exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 1 (id (Nat.ModEq.symm this)))
      simp
      exact g
    rw [g] at h1
    simp at h1
    clear g
    subst m
    suffices ∑ i ∈ Finset.range (4 * n + 2 + 1), 22 ^ 2 ^ (i + 1) ≡ 76 + 4 * n [MOD 100] by exact Nat.ModEq.trans h8 this
    clear h h8
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [show 4 * (n + 1) + 2 + 1 = 4 * n + 7 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 4 * n + 4 + 1 = 4 * n + 5 by omega]
      rw [show 4 * n + 3 + 1 = 4 * n + 4 by omega]
      rw [show 4 * n + 6 + 1 = 4 * (n + 1) + 3 by omega]
      rw [show 4 * n + 5 + 1 = 4 * (n + 1) + 2 by omega]
      replace h4:= h4 (n + 1)
      replace h5:= h5 (n + 1)
      replace h6:= h6 n
      replace h7:= h7 n
      replace ih:= Nat.ModEq.add ih h6
      replace ih:= Nat.ModEq.add ih h7
      replace ih:= Nat.ModEq.add ih h4
      replace ih:= Nat.ModEq.add ih h5
      rw [show 4 * n + 2 + 1 = 4 * n + 3 by omega] at ih
      have g1 : 76 + 4 * n + 96 + 16 + 56 + 36 ≡ 76 + 4 * (n + 1) [MOD 100]:= by
        rw [show 76 + 4 * (n + 1) = 76 + 4 * (n + 1) + 0 by ring]
        rw [show 76 + 4 * n + 96 + 16 + 56 + 36 = 76 + 4 * (n + 1) + 200 by ring]
        have g2 : 200 ≡ 0 [MOD 100]:= by rfl
        exact Nat.ModEq.add rfl g2
      exact Nat.ModEq.trans ih g1
  .
    -- Case 4: n ≡ 0 [MOD 4] implies S ≡ 72 + 4*((n-1)/4) [MOD 100]
    intro g
    replace g : m ≡ 3 [MOD 4]:= by
      suffices m + 1 ≡ 3 + 1 [MOD 4] by exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 1 (id (Nat.ModEq.symm this)))
      simp
      exact g
    rw [g] at h1
    simp at h1
    clear g
    subst m
    suffices ∑ i ∈ Finset.range (4 * n + 3 + 1), 22 ^ 2 ^ (i + 1) ≡ 72 + 4 * n [MOD 100] by exact Nat.ModEq.trans h8 this
    clear h h8
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      rw [show 4 * (n + 1) + 3 + 1 = 4 * n + 8 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [show 4 * n + 4 + 1 = 4 * n + 5 by omega]
      rw [show 4 * n + 7 + 1 = 4 * (n + 1) + 4 by omega]
      rw [show 4 * n + 6 + 1 = 4 * (n + 1) + 3 by omega]
      rw [show 4 * n + 5 + 1 = 4 * (n + 1) + 2 by omega]
      replace h4:= h4 (n + 1)
      replace h5:= h5 (n + 1)
      replace h6:= h6 (n + 1)
      replace h7:= h7 n
      replace ih:= Nat.ModEq.add ih h7
      replace ih:= Nat.ModEq.add ih h4
      replace ih:= Nat.ModEq.add ih h5
      replace ih:= Nat.ModEq.add ih h6
      rw [show 4 * n + 3 + 1 = 4 * n + 4 by omega] at ih
      have g1 : 72 + 4 * n + 16 + 56 + 36 + 96 ≡ 72 + 4 * (n + 1) [MOD 100]:= by
        rw [show 72 + 4 * (n + 1) = 72 + 4 * (n + 1) + 0 by ring]
        rw [show 72 + 4 * n + 16 + 56 + 36 + 96 = 72 + 4 * (n + 1) + 200 by ring]
        have g2 : 200 ≡ 0 [MOD 100]:= by rfl
        exact Nat.ModEq.add rfl g2
      exact Nat.ModEq.trans ih g1
