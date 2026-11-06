import Mathlib
/- Let $M$ be a positive integer. Let the sequence of integers $A_k$ be defined by $A_642002 = 1$ and $A_k = 10 \cdot A_{k-1} + k$ for all integers $k \ge 2$.
Determine the remainder when the sum $S_M = \sum_{k=1}^{M} A_k$ is divided by $5$.
Show that this remainder is $R_M$, where
$R_M = 0$ if $M \pmod 5 = 0$ or $M \pmod 5 = 4$;
$R_M = 1$ if $M \pmod 5 = 1$ or $M \pmod 5 = 3$;
$R_M = 3$ if $M \pmod 5 = 2$. -/
theorem number_theory_642002 (a S : ℕ → ℕ) (h1 : a 0 = 1) (hn : ∀ n : ℕ, a (n + 1) = 10 * a n + (n + 2)) (hSn : ∀ n : ℕ, S n = ∑ i in Finset.range n, a i) : ∀ n : ℕ, (n ≡ 0 [MOD 5] ∨ n ≡ 4 [MOD 5] → (S n) % 5 = 0) ∧ (n ≡ 1 [MOD 5] ∨ n ≡ 3 [MOD 5] → (S n) % 5 = 1) ∧ (n ≡ 2 [MOD 5] → (S n) % 5 = 3):= by

  -- Key lemma: For all n, 2*S_n ≡ n*(n+1) (mod 5)
  -- This is proved by induction on n
  have h2 : ∀ n : ℕ, 2 * S n ≡ n * (n + 1) [MOD 5]:= by
    intro n
    induction n with
    | zero =>
      simp [hSn]
      rfl
    | succ n ih =>
      simp [hSn]
      rw [Finset.sum_range_succ]
      rw [show 2 * (∑ x ∈ Finset.range n, a x + a n) = 2 * (∑ x ∈ Finset.range n, a x) + 2 * a n by ring]
      rw [←hSn n]
      specialize hn (n - 1)
      by_cases hn0 : n = 0
      .
        subst n
        simp [hSn, h1]
        rfl
      .
        rw [show n - 1 + 1 = n by omega] at hn
        rw [show n - 1 + 2 = n + 1 by omega] at hn

        -- Key observation: 10*a_(n-1) ≡ 0 (mod 5)
        have g1 : 10 * a (n - 1) ≡ 0 [MOD 5]:= by
          suffices 5 ∣ 10 * a (n - 1) by exact Nat.modEq_zero_iff_dvd.mpr this
          use 2 * a (n - 1)
          ring
        replace g1 : 10 * a (n - 1) + (n + 1) ≡ 0 + (n + 1) [MOD 5]:= by exact Nat.ModEq.add_right (n + 1) g1
        simp at g1
        rw [←hn] at g1
        replace g1 : 2 * a n ≡ 2 * (n + 1) [MOD 5]:= by exact Nat.ModEq.mul rfl g1
        rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring]
        exact Nat.ModEq.add ih g1
  clear h1 hn hSn

  -- Main proof: Using the key lemma to prove the three cases
  intro n
  specialize h2 n
  refine ⟨?_, ?_, ?_⟩
  .
    -- Case 1: n ≡ 0 or 4 (mod 5) implies S_n ≡ 0 (mod 5)
    intro h
    rcases h with h | h
    .
      suffices 5 ∣ S n by exact Nat.dvd_iff_mod_eq_zero.mp this
      replace h : n * (n + 1) ≡ 0 * (n + 1) [MOD 5]:= by exact Nat.ModEq.mul h rfl
      simp at h
      replace h2 : 2 * S n ≡ 0 [MOD 5]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) (id (Nat.ModEq.symm h2)))
      replace h2 : 5 ∣ 2 * S n:= by exact Nat.dvd_of_mod_eq_zero h2
      have g1 : Nat.Coprime 5 2:= by norm_num
      exact Nat.Coprime.dvd_of_dvd_mul_left g1 h2
    .
      replace h : n + 1 ≡ 4 + 1 [MOD 5]:= by exact Nat.ModEq.add h rfl
      simp at h
      replace h : 5 ∣ n + 1:= by exact Nat.dvd_of_mod_eq_zero h
      replace h : 5 ∣ n * (n + 1):= by exact Dvd.dvd.mul_left h n
      replace h : n * (n + 1) ≡ 0 [MOD 5]:= by exact Nat.modEq_zero_iff_dvd.mpr h
      replace h2 : 2 * S n ≡ 0 [MOD 5]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h)) (id (Nat.ModEq.symm h2)))
      suffices 5 ∣ S n by exact Nat.dvd_iff_mod_eq_zero.mp this
      replace h2 : 5 ∣ 2 * S n:= by exact Nat.dvd_of_mod_eq_zero h2
      have g1 : Nat.Coprime 5 2:= by norm_num
      exact Nat.Coprime.dvd_of_dvd_mul_left g1 h2
  .
    -- Case 2: n ≡ 1 or 3 (mod 5) implies S_n ≡ 1 (mod 5)
    intro h
    suffices S n ≡ 1 [MOD 5] by exact this
    have g1 : Nat.Coprime 5 2:= by norm_num
    suffices 2 * S n ≡ 2 * 1 [MOD 5] by exact Nat.ModEq.cancel_left_of_coprime g1 this
    suffices n * (n + 1) ≡ 2 [MOD 5] by exact Nat.ModEq.trans h2 this

    rcases h with h | h
    .
      have h1 : n ≥ n % 5:= by exact Nat.mod_le n 5
      rw [h] at h1
      simp at h1
      replace h : 5 ∣ n - 1:= by exact (Nat.modEq_iff_dvd' h1).mp (id (Nat.ModEq.symm h))
      have h3 : n * (n + 1) = (n - 1) * (n + 2) + 2:= by
        set m:= n - 1 with hm
        clear_value m
        replace hm : n = m + 1:= by omega
        subst n
        ring_nf
      rw [show 2 = 0 + 2 by simp]
      rw [h3]
      suffices (n - 1) * (n + 2) ≡ 0 [MOD 5] by exact Nat.ModEq.add this rfl
      suffices 5 ∣ (n - 1) * (n + 2) by exact Nat.modEq_zero_iff_dvd.mpr this
      exact Dvd.dvd.mul_right h (n + 2)
    .
      replace h : n + 2 ≡ 3 + 2 [MOD 5]:= by exact Nat.ModEq.add h rfl
      simp at h
      replace h : 5 ∣ n + 2:= by exact Nat.dvd_of_mod_eq_zero h
      have h3 : n * (n + 1) = (n - 1) * (n + 2) + 2:= by
        set m:= n - 1 with hm
        clear_value m
        replace hm : n = m + 1:= by omega
        subst n
        ring_nf
      rw [show 2 = 0 + 2 by simp]
      rw [h3]
      suffices (n - 1) * (n + 2) ≡ 0 [MOD 5] by exact Nat.ModEq.add this rfl
      suffices 5 ∣ (n - 1) * (n + 2) by exact Nat.modEq_zero_iff_dvd.mpr this
      exact Dvd.dvd.mul_left h (n - 1)
  .
    -- Case 3: n ≡ 2 (mod 5) implies S_n ≡ 3 (mod 5)
    intro h
    suffices S n ≡ 3 [MOD 5] by exact this
    have g1 : Nat.Coprime 5 2:= by norm_num
    suffices 2 * S n ≡ 2 * 3 [MOD 5] by exact Nat.ModEq.cancel_left_of_coprime g1 this
    suffices n * (n + 1) ≡ 6 [MOD 5] by exact Nat.ModEq.trans h2 this
    have h1 : n ≥ n % 5:= by exact Nat.mod_le n 5
    rw [h] at h1
    simp at h1
    replace h : 5 ∣ n - 2:= by exact (Nat.modEq_iff_dvd' h1).mp (id (Nat.ModEq.symm h))
    have h3 : n * (n + 1) = (n - 2) * (n + 3) + 6:= by
      set m:= n - 2 with hm
      clear_value m
      replace hm : n = m + 2:= by omega
      subst n
      ring_nf
    rw [show 6 = 0 + 6 by simp]
    rw [h3]
    suffices (n - 2) * (n + 3) ≡ 0 [MOD 5] by exact Nat.ModEq.add this rfl
    suffices 5 ∣ (n - 2) * (n + 3) by exact Nat.modEq_zero_iff_dvd.mpr this
    exact Dvd.dvd.mul_right h (n + 3)
