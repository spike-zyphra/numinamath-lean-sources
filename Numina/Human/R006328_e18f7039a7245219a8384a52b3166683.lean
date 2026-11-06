import Mathlib
/- Let $K$ be an integer such that $K \ge 13$. Let $P_K = \prod_{i=0}^{K-1} (2i+1)$.
Let $r = K \pmod 4$.
Let $v_8$ be a value defined as follows:
if $r=0$ or $r=1$, then $v_635929 = 1$;
if $r=2$, then $v_635929 = 3$;
if $r=3$, then $v_635929 = 7$.
Show that $P_K \pmod{1000} = (125 \cdot ( (5 \cdot v_8) \bmod 8))$. -/
theorem number_theory_635929 (k p : ℕ) (hk : k ≥ 13) (hp : p = ∏ i in Finset.range k, (2 * i + 1)) : (k ≡ 0 [MOD 4] ∨ k ≡ 1 [MOD 4] → p % 1000 = 125 * ((5 * 1) % 8)) ∧ (k ≡ 2 [MOD 4] → p % 1000 = 125 * ((5 * 3) % 8)) ∧ (k ≡ 3 [MOD 4] → p % 1000 = 125 * ((5 * 7) % 8)):= by
  -- Lemma 1: For any n, 125 divides the product of (2i+1) from i=0 to n+12
  have h1 : ∀ n : ℕ, 125 ∣ ∏ i in Finset.range (n + 13), (2 * i + 1):= by
    intro n
    induction n with
    | zero =>
      simp [Finset.prod_range_succ]
      omega
    | succ n ih =>
      rw [Finset.prod_range_succ]
      rcases ih with ⟨t, ht⟩
      use t * (2 * (n + 13) + 1)
      rw [ht]
      ring
  -- Apply the lemma to k-13 to get 125 divides our product
  specialize h1 (k - 13)
  rw [show k - 13 + 13 = k by omega] at h1
  -- Convert divisibility to congruence modulo 125
  replace h1 : ∏ i ∈ Finset.range k, (2 * i + 1) ≡ 625 [MOD 125]:= by exact Nat.modEq_zero_iff_dvd.2 h1

  -- Lemma 2: For any n, m, we have 2n + m ≡ 2(n mod 4) + m (mod 8)
  have h2 : ∀ n m : ℕ, 2 * n + m ≡  2 * (n % 4) + m [MOD 8]:= by
    intro n m
    -- Express n as 4q + r where r = n mod 4
    have h2 : 2 * n + m = 8 * (n / 4) + (2 * (n % 4) + m):= by omega
    rw [show 2 * (n % 4) + m = 0 + (2 * (n % 4) + m) by simp]
    rw [h2]
    -- Show that 8 * (n / 4) ≡ 0 (mod 8)
    have h3 : 8 * (n / 4) ≡ 0 [MOD 8]:= by
      suffices 8 ∣ 8 * (n / 4) by exact Nat.modEq_zero_iff_dvd.mpr this
      simp
    exact Nat.ModEq.add h3 rfl

  -- Express k as 4t + r where r = k mod 4
  have h3 : k = 4 * (k / 4) + (k % 4):= by omega
  set t:= k / 4
  clear_value t

  -- Lemma 3: For any m, the product of (2i+1) from i=0 to 4m-1 is congruent to 625 modulo 8
  have h4 : ∀ m : ℕ, ∏ i ∈ Finset.range (4 * m), (2 * i + 1) ≡ 625 [MOD 8]:= by
    intro m
    induction m with
    | zero =>
      simp
      rfl
    | succ m ih =>
      -- Expand 4(m+1) as 4m + 4
      rw [show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by omega]
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      rw [Finset.prod_range_succ]
      -- Simplify the expressions for the last four terms
      rw [show 2 * (4 * m + 1) + 1 = 2 * (4 * m) + 3 by omega]
      rw [show 2 * (4 * m + 2) + 1 = 2 * (4 * m) + 5 by omega]
      rw [show 2 * (4 * m + 3) + 1 = 2 * (4 * m) + 7 by omega]
      -- Apply Lemma 2 to each of the four terms
      have g1:= h2 (4 * m) 1
      have g2:= h2 (4 * m) 3
      have g3:= h2 (4 * m) 5
      have g4:= h2 (4 * m) 7
      have g : (4 * m) % 4 = 0:= by omega
      rw [g] at g1 g2 g3 g4
      simp at g1 g2 g3 g4
      -- Multiply the congruences together
      replace g:= Nat.ModEq.mul ih g1
      replace g:= Nat.ModEq.mul g g2
      replace g:= Nat.ModEq.mul g g3
      replace g:= Nat.ModEq.mul g g4
      simp at g
      exact g

  -- Split into three cases based on k mod 4
  refine ⟨?_, ?_, ?_⟩
  .
    -- Case 1: k ≡ 0 or 1 (mod 4)
    intro h
    rcases h with h | h
    .
      -- Subcase 1a: k ≡ 0 (mod 4)
      rw [h] at h3
      simp at h3
      simp
      rw [show 625 = 625 % 1000 by simp]
      subst k p
      specialize h4 t
      rw [show 1000 = 8 * 125 by omega]
      have g : Nat.Coprime 8 125:= by decide
      exact (Nat.modEq_and_modEq_iff_modEq_mul g).mp ⟨h4, h1⟩
    .
      -- Subcase 1b: k ≡ 1 (mod 4)
      rw [h] at h3
      simp at h3
      simp
      rw [show 625 = 625 % 1000 by simp]
      subst k p
      specialize h4 t
      specialize h2 (4 * t) 1
      rw [show (4 * t) % 4 = 0 by omega] at h2
      simp at h2
      replace h4:= Nat.ModEq.mul h4 h2
      rw [←Finset.prod_range_succ] at h4
      simp at h4
      rw [show 1000 = 8 * 125 by omega]
      have g : Nat.Coprime 8 125:= by decide
      exact (Nat.modEq_and_modEq_iff_modEq_mul g).mp ⟨h4, h1⟩
  .
    -- Case 2: k ≡ 2 (mod 4)
    intro h
    rw [h] at h3
    simp at h3
    simp
    rw [show 875 = 875 % 1000 by simp]
    subst k p
    specialize h4 t
    have g1:= h2 (4 * t) 1
    have g2:= h2 (4 * t) 3
    rw [show (4 * t) % 4 = 0 by omega] at g1 g2
    simp at g1 g2
    rw [show 2 * (4 * t) + 3 = 2 * (4 * t + 1) + 1 by omega] at g2
    replace h4:= Nat.ModEq.mul h4 g1
    rw [←Finset.prod_range_succ] at h4
    replace h4:= Nat.ModEq.mul h4 g2
    rw [←Finset.prod_range_succ] at h4
    simp at h4
    rw [show 1000 = 8 * 125 by omega]
    have g : Nat.Coprime 8 125:= by decide
    exact (Nat.modEq_and_modEq_iff_modEq_mul g).mp ⟨h4, h1⟩
  .
    -- Case 3: k ≡ 3 (mod 4)
    intro h
    rw [h] at h3
    simp at h3
    simp
    rw [show 375 = 375 % 1000 by simp]
    subst k p
    specialize h4 t
    have g1:= h2 (4 * t) 1
    have g2:= h2 (4 * t) 3
    have g3:= h2 (4 * t) 5
    rw [show (4 * t) % 4 = 0 by omega] at g1 g2
    simp at g1 g2 g3
    rw [show 2 * (4 * t) + 3 = 2 * (4 * t + 1) + 1 by omega] at g2
    rw [show 2 * (4 * t) + 5 = 2 * (4 * t + 2) + 1 by omega] at g3
    replace h4:= Nat.ModEq.mul h4 g1
    rw [←Finset.prod_range_succ] at h4
    replace h4:= Nat.ModEq.mul h4 g2
    rw [←Finset.prod_range_succ] at h4
    replace h4:= Nat.ModEq.mul h4 g3
    rw [←Finset.prod_range_succ] at h4
    simp at h4
    rw [show 1000 = 8 * 125 by omega]
    have g : Nat.Coprime 8 125:= by decide
    exact (Nat.modEq_and_modEq_iff_modEq_mul g).mp ⟨h4, h1⟩
