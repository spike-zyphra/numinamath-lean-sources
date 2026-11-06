import Mathlib
/- Let $N$ be a positive integer such that $N > 1$ and $N \equiv 1 \pmod 3$. Let $S_0$ be the number consisting of $N$ repetitions of the digit $1$. Define a sequence $(S_k)_{k \ge 0}$ by $S_{k+1} = 4 \cdot (S_k \text{ div } 10) + (S_k \text{ mod } 10)$. Let $S_m$ be the first term in this sequence that is a single-digit number (i.e., $0 \le S_m \le 9$). Show that $S_m=7$. -/
theorem algebra_637351 (S : ℕ → ℕ) (n m : ℕ) (hn : n > 1) (h1 : n ≡ 1 [MOD 3]) (h2 : S 0 = ∑ i in Finset.range n, 10 ^ i) (hS : ∀ k : ℕ, S (k + 1) = 4 * (S k / 10) + (S k % 10)) (hm : IsLeast {k : ℕ | S k < 10} m) : S m = 7:= by
  -- Prove that S_k ≡ S_0 (mod 3) for all k by induction
  have h3 : ∀ k : ℕ, S k ≡ S 0 [MOD 3]:= by
    intro k
    induction k with
    | zero =>
      rfl
    | succ k ih =>
      rw [hS k]
      -- Use the fact that S_k = 10*(S_k div 10) + (S_k mod 10)
      have g : S k = 10 * (S k / 10) + (S k % 10):= by omega
      rw [g] at ih
      -- Since 10 ≡ 4 (mod 3), we can replace 10 with 4 in the congruence
      have g1 : 10 ≡ 4 [MOD 3]:= by rfl
      replace g1 : 10 * (S k / 10) ≡ 4 * (S k / 10) [MOD 3]:= by exact Nat.ModEq.mul g1 rfl
      replace g1 : 10 * (S k / 10) + (S k % 10) ≡ 4 * (S k / 10) + (S k % 10) [MOD 3]:= by exact Nat.ModEq.add g1 rfl
      exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm ih)) g1)

  -- Prove that S_k ≡ S_0 (mod 2) for all k by induction
  have h4 : ∀ k : ℕ, S k ≡ S 0 [MOD 2]:= by
    intro k
    induction k with
    | zero =>
      rfl
    | succ k ih =>
      rw [hS k]
      -- 4*(S_k div 10) is always even (divisible by 2)
      have g : 4 * (S k / 10) ≡ 0 [MOD 2]:= by
        suffices 2 ∣ 4 * (S k / 10) by exact Nat.modEq_zero_iff_dvd.mpr this
        omega
      replace g1 : 4 * (S k / 10) + (S k % 10) ≡ 0 + (S k % 10) [MOD 2]:= by exact Nat.ModEq.add g rfl
      simp at g1
      -- Show that S_k mod 10 ≡ S_k (mod 2)
      have g2 : S k % 10 ≡ S k [MOD 2]:= by
        have g3 : S k = 10 * (S k / 10) + (S k % 10):= by omega
        have g4 : 10 ≡ 0 [MOD 2]:= by rfl
        replace g4 : 10 * (S k / 10) ≡ 0 * (S k / 10) [MOD 2]:= by exact Nat.ModEq.mul g4 rfl
        simp at g4
        replace g4 : 10 * (S k / 10) + (S k % 10) ≡ 0 + (S k % 10) [MOD 2]:= by exact Nat.ModEq.add g4 rfl
        simp at g4
        rw [←g3] at g4
        exact id (Nat.ModEq.symm g4)
      replace g1 : 4 * (S k / 10) + S k % 10 ≡ S k [MOD 2]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm g2)) (id (Nat.ModEq.symm g1)))
      exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm ih)) (id (Nat.ModEq.symm g1)))

  -- Extract the two conditions from IsLeast
  rcases hm with ⟨hm1, hm2⟩

  -- Prove that m > 0 (the first single-digit term is not S_0)
  have h5 : m > 0:= by
    by_contra H
    simp at H
    subst m
    simp at hm1
    -- Show that S_0 ≥ 11 (since n > 1, S_0 has at least 2 digits)
    have h5 : S 0 ≥ 11:= by
      rw [h2]
      set n1:= n - 2 with hn1
      clear_value n1
      replace hn1 : n = n1 + 2:= by omega
      subst n
      rw [Finset.sum_range_succ] at h2
      rw [Finset.sum_range_succ] at h2
      rw [show 10 ^ (n1 + 1) = 10 * 10 ^ n1 by omega] at h2
      have g : 10 ^ n1 > 0:= by positivity
      omega
    linarith

  -- Extract the lower bound condition
  simp [lowerBounds] at hm2

  -- Prove that S_(m-1) ≥ 10 (the term before the first single-digit term)
  have h6 : S (m - 1) ≥ 10:= by
    by_contra H
    simp at H
    replace hm2:= hm2 H
    omega

  -- Show that S_m ≡ 1 (mod 3)
  replace h3 : S m ≡ 1 [MOD 3]:= by
    replace h3:= h3 m
    suffices S 0 ≡ 1 [MOD 3] by exact Nat.ModEq.trans h3 this
    rw [h2]
    -- Prove that sum of powers of 10 ≡ k (mod 3)
    have h7 : ∀ k : ℕ, ∑ i ∈ Finset.range k, 10 ^ i ≡ k [MOD 3]:= by
      intro k
      induction k with
      | zero =>
        simp
        rfl
      | succ k ih =>
        rw [Finset.sum_range_succ]
        suffices 10 ^ k ≡ 1 [MOD 3] by exact Nat.ModEq.add ih this
        rw [show 1 = 1 ^ k by simp]
        suffices 10 ≡ 1 [MOD 3] by exact Nat.ModEq.pow k this
        rfl
    replace h7:= h7 n
    exact Nat.ModEq.trans h7 h1

  -- Show that S_m ≡ 1 (mod 2)
  replace h4 : S m ≡ 1 [MOD 2]:= by
    replace h4:= h4 m
    suffices S 0 ≡ 1 [MOD 2] by exact Nat.ModEq.trans h4 this
    rw [h2]
    -- Prove that sum of powers of 10 ≡ 1 (mod 2) for n terms
    have h7 : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), 10 ^ i ≡ 1 [MOD 2]:= by
      intro k
      induction k with
      | zero =>
        simp
        rfl
      | succ k ih =>
        rw [Finset.sum_range_succ]
        -- 10^(k+1) is even (divisible by 2)
        have g : 10 ^ (k + 1) ≡ 0 [MOD 2]:= by
          suffices 2 ∣ 10 ^ (k + 1) by exact Nat.modEq_zero_iff_dvd.mpr this
          ring_nf
          use 5 * 10 ^ k
          ring
        replace ih:= Nat.ModEq.add ih g
        simp at ih
        exact ih
    specialize h7 (n - 1)
    rw [show n - 1 + 1 = n by omega] at h7
    exact h7

  -- Extract the condition that S_m < 10
  simp at hm1

  -- Prove that S_m ≥ 1 (since S_m ≡ 1 (mod 2))
  have h7 : S m ≥ 1:= by
    have g : S m ≥ S m % 2:= by exact Nat.mod_le (S m) 2
    rw [h4] at g
    simp at g
    exact g

  -- Convert congruences to divisibility conditions
  replace h3 : 3 ∣ S m - 1:= by exact (Nat.modEq_iff_dvd' h7).mp (id (Nat.ModEq.symm h3))
  replace h4 : 2 ∣ S m - 1:= by exact (Nat.modEq_iff_dvd' h7).mp (id (Nat.ModEq.symm h4))

  -- Since 2 and 3 are coprime, 6 divides S_m - 1
  have g : Nat.Coprime 2 3:= by norm_num
  replace h3 : 2 * 3 ∣ S m - 1:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g h4 h3
  simp at h3

  -- This means S_m = 6k + 1 for some k
  rcases h3 with ⟨k, hk⟩
  replace hk : S m = 6 * k + 1:= by omega

  -- Since S_m < 10, k can only be 0 or 1
  replace g : k = 0 ∨ k = 1:= by omega
  rcases g with g | g
  .
    -- Case k = 0: S_m = 1, but this contradicts S_(m-1) ≥ 10
    subst k
    simp at hk
    specialize hS (m - 1)
    rw [show m - 1 + 1 = m by omega] at hS
    replace h6 : S (m - 1) / 10 ≥ 1:= by omega
    omega
  .
    -- Case k = 1: S_m = 7, which is what we wanted to prove
    subst k
    simp at hk
    exact hk
