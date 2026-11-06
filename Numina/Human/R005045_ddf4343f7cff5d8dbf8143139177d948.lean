import Mathlib
/- Consider the function $f: \mathbb{N}_{0} \rightarrow \mathbb{N}_{0}$, where $\mathbb{N}_{0}$ is the set of all non-negative integers, defined by the following conditions:
(i) $f(0)=0$,
(ii) $f(2 n)=2 f(n)$ and
(iii) $f(2 n+1)=n+2 f(n)$ for all $n \geq 0$.
(a) Determine the three sets $L:=\{n \mid f(n)<f(n+1)\}, E:=\{n \mid f(n)=f(n+1)\}$, and $G:=\{n \mid f(n)>f(n+1)\}$.
(b) For each $k \geq 0$, find a formula for $a_{k}:=\max \left\{f(n): 0 \leq n \leq 2^{k}\right\}$ in terms of $k$. -/
theorem number_theory_605259 (f : ℕ → ℕ) (h1 : f 0 = 0) (h2 : ∀ n : ℕ, f (2 * n) = 2 * f n) (h3 : ∀ n : ℕ, f (2 * n + 1) = n + 2 * f n) : {n : ℕ | f n < f (n + 1)} = {n : ℕ | ∃ k : ℕ, n = 2 * k + 2} ∧ {n : ℕ | f n = f (n + 1)} = {n : ℕ | n = 0 ∨ (∃ k : ℕ, n = 4 * k + 1)} ∧ {n : ℕ | f n > f (n + 1)} = {n : ℕ | ∃ k : ℕ, n = 4 * k + 3} ∧ (∀ k : ℕ, IsGreatest {S | ∃ n : ℕ, n ≤ 2 ^ k ∧ S = f n} (k * 2 ^ (k - 1) + 1 - 2 ^ k)):= by

  -- Step 1: Prove that numbers of form 2k+2 are in the increasing set L
  have g1 : {n : ℕ | ∃ k : ℕ, n = 2 * k + 2} ⊆ {n : ℕ | f n < f (n + 1)}:= by
    intro n hn
    simp at hn ⊢
    rcases hn with ⟨k, rfl⟩
    replace h2:= h2 (k + 1)
    replace h3:= h3 (k + 1)
    rw [←h2] at h3
    ring_nf at h3 ⊢
    linarith

  -- Step 2: Prove that numbers of form 0 or 4k+1 are in the equal set E
  have g2 : {n : ℕ | n = 0 ∨ (∃ k : ℕ, n = 4 * k + 1)} ⊆ {n : ℕ | f n = f (n + 1)}:= by
    intro n hn
    simp at hn ⊢
    rcases hn with rfl | ⟨k, rfl⟩
    simp [h3 0]
    linarith
    have g:= h3 k
    replace h3:= h3 (2 * k)
    rw [h2 k] at h3
    rw [show 2 * (2 * k) + 1 = 4 * k + 1 by omega] at h3
    rw [show 4 * k + 1 + 1 = 2 * (2 * k + 1) by omega]
    rw [h2 (2 * k + 1), h3, g]
    ring

  -- Step 3: Prove that numbers of form 4k+3 are in the decreasing set G
  have g3 : {n : ℕ | ∃ k : ℕ, n = 4 * k + 3} ⊆ {n : ℕ | f n > f (n + 1)}:= by
    -- First prove a key lemma: f(n+1) ≤ f(n) + n for all n
    have g3 : ∀ m : ℕ, ∀ n : ℕ, n ≤ m → f (n + 1) ≤ f n + n:= by
      intro m
      induction m with
      | zero =>
        intro n hn
        simp at hn
        subst n
        simp [h3 0, h1]
      | succ m ih =>
        intro n hn
        by_cases hn : Even n
        .
          rcases hn with ⟨k, rfl⟩
          rw [show k + k = 2 * k by omega]
          rw [h2 k, h3 k]
          linarith
        .
          simp at hn
          rcases hn with ⟨k, rfl⟩
          rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
          rw [h2 (k + 1), h3 k]
          replace ih:= ih k (by omega)
          linarith
    intro n hn
    simp at hn ⊢
    rcases hn with ⟨k, rfl⟩
    rw [show 4 * k + 3 + 1 = 2 * (2 * (k + 1)) by omega]
    rw [show 4 * k + 3 = 2 * (2 * k + 1) + 1 by omega]
    rw [h2 (2 * (k + 1)), h2 (k + 1), h3 (2 * k + 1), h3 k]
    replace g3:= g3 k k (by omega)
    linarith

  -- Step 4: Prove the reverse inclusion for the increasing set L
  replace g1 : {n : ℕ | f n < f (n + 1)} = {n : ℕ | ∃ k : ℕ, n = 2 * k + 2}:= by
    suffices {n : ℕ | f n < f (n + 1)} ⊆ {n : ℕ | ∃ k : ℕ, n = 2 * k + 2} by exact Set.Subset.antisymm this g1
    intro n hn
    simp at hn ⊢
    have hne : n ≠ 0:= by
      by_contra H
      subst n
      simp [h3 0, h1] at hn
    mod_cases n % 4
    .
      replace H : 4 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
      rcases H with ⟨k, hk⟩
      replace hne : k ≠ 0:= by omega
      set k1:= k - 1 with hk1
      clear_value k1
      replace hk1 : k = k1 + 1:= by omega
      subst k
      use 2 * k1 + 1
      linarith
    all_goals
      have g : n ≥ n % 4:= by exact Nat.mod_le n 4
      rw [H] at g
      simp at g
      replace H:= (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm H))
      rcases H with ⟨k, hk⟩
    .
      replace hk : n = 4 * k + 1:= by rw [←hk] ; omega
      replace hk : n ∈ {n | n = 0 ∨ ∃ k, n = 4 * k + 1}:= by
        simp
        right
        subst n
        use k
      replace g2:= g2 hk
      simp at g2
      linarith
    .
      replace hk : n = 4 * k + 2:= by rw [←hk] ; omega
      use 2 * k
      subst n
      ring
    .
      replace hk : n = 4 * k + 3:= by rw [←hk] ; omega
      replace hk : n ∈ {n | ∃ k, n = 4 * k + 3}:= by
        subst n
        simp
      replace g3:= g3 hk
      simp at g3
      linarith

  -- Step 5: Prove the reverse inclusion for the equal set E
  replace g2 : {n : ℕ | f n = f (n + 1)} = {n : ℕ | n = 0 ∨ (∃ k : ℕ, n = 4 * k + 1)}:= by
    suffices {n : ℕ | f n = f (n + 1)} ⊆ {n : ℕ | n = 0 ∨ (∃ k : ℕ, n = 4 * k + 1)} by exact Set.Subset.antisymm this g2
    intro n hn
    simp at hn ⊢
    by_cases hn : n = 0
    .
      subst n
      simp
    .
      mod_cases n % 4
      .
        replace H : 4 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
        rcases H with ⟨k, hk⟩
        replace hk : n = 4 * k:= by omega
        set k1:= k - 1 with hk1
        clear_value k1
        replace hk1 : k = k1 + 1:= by omega
        subst k
        replace hk : n ∈ {n | f n < f (n + 1)}:= by
          subst n
          rw [g1]
          simp
          use 2 * k1 + 1
          ring
        simp at hk
        linarith
      all_goals
        have g : n ≥ n % 4:= by exact Nat.mod_le n 4
        rw [H] at g
        simp at g
        replace H:= (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm H))
        rcases H with ⟨k, hk⟩
      .
        replace hk : n = 4 * k + 1:= by rw [←hk] ; omega
        right
        subst n
        simp
      .
        replace hk : n = 4 * k + 2:= by rw [←hk] ; omega
        replace hk : n ∈ {n | f n < f (n + 1)}:= by
          subst n
          rw [g1]
          simp
          use 2 * k
          ring
        simp at hk
        linarith
      .
        replace hk : n = 4 * k + 3:= by rw [←hk] ; omega
        replace hk : n ∈ {n | ∃ k, n = 4 * k + 3}:= by
          subst n
          simp
        replace g3:= g3 hk
        simp at g3
        linarith

  -- Step 6: Prove the reverse inclusion for the decreasing set G
  replace g3 : {n : ℕ | f n > f (n + 1)} = {n : ℕ | ∃ k : ℕ, n = 4 * k + 3}:= by
    suffices {n : ℕ | f n > f (n + 1)} ⊆ {n : ℕ | ∃ k : ℕ, n = 4 * k + 3} by exact Set.Subset.antisymm this g3
    intro n h
    simp at h ⊢
    by_cases hn : n = 0
    .
      subst n
      replace g2 : 0 ∈ {n | f n = f (n + 1)}:= by
        rw [g2]
        simp
      simp at g2
      simp at h
      linarith
    .
      mod_cases n % 4
      .
        replace H : 4 ∣ n:= by exact Nat.dvd_of_mod_eq_zero H
        rcases H with ⟨k, hk⟩
        replace hk : n = 4 * k:= by omega
        set k1:= k - 1 with hk1
        clear_value k1
        replace hk1 : k = k1 + 1:= by omega
        subst k
        replace g1 : n ∈ {n | f n < f (n + 1)}:= by
          rw [g1]
          subst n
          simp
          use 2 * k1 + 1
          ring
        simp at g1
        linarith
      all_goals
        have g : n ≥ n % 4:= by exact Nat.mod_le n 4
        rw [H] at g
        simp at g
        replace H:= (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm H))
        rcases H with ⟨k, hk⟩
      .
        replace hk : n = 4 * k + 1:= by rw [←hk] ; omega
        replace g2 : n ∈ {n | f n = f (n + 1)}:= by
          rw [g2]
          subst n
          simp
        simp at g2
        linarith
      .
        replace hk : n = 4 * k + 2:= by rw [←hk] ; omega
        replace g1 : n ∈ {n | f n < f (n + 1)}:= by
          rw [g1]
          subst n
          simp
          use 2 * k
          ring
        simp at g1
        linarith
      .
        replace hk : n = 4 * k + 3:= by rw [←hk] ; omega
        subst n
        simp

  -- Step 7: Prove the maximum value formula for part (b)
  refine ⟨g1, g2, g3, ?_⟩

  -- Prove that f(2^k - 1) is the maximum value in the range [0, 2^k]
  have h4 : ∀ k : ℕ, IsGreatest {S : ℕ | ∃ n ≤ 2 ^ k, S = f n} (f (2 ^ k - 1)):= by
    intro k
    induction k with
    | zero =>
      simp
      constructor
      .
        simp
        use 0
        simp
      .
        simp [upperBounds]
        intro S x hx hS
        subst S
        replace hx : x = 0 ∨ x = 1:= by exact Nat.le_one_iff_eq_zero_or_eq_one.mp hx
        rcases hx with rfl | rfl
        .
          simp
        .
          simp [h3 0, h1]
    | succ k ih =>
      constructor
      .
        simp
        use (2 ^ (k + 1) - 1)
        simp
      .
        simp [upperBounds]
        intro S x hx hS
        subst S
        rcases ih with ⟨-, ih⟩
        simp [upperBounds] at ih
        by_cases hx1 : Odd x
        .
          rcases hx1 with ⟨x, rfl⟩
          rw [h3]
          have g : x ≤ 2 ^ k:= by
            ring_nf at hx
            linarith
          replace ih:= ih x g (show f x = f x by simp)
          have g0 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1:= by
            ring_nf
            have h4 : 2 ^ k > 0:= by positivity
            omega
          rw [g0, h3 (2 ^ k - 1)]
          replace hx : x ≤ 2 ^ k - 1:= by
            ring_nf at hx
            omega
          linarith
        .
          simp at hx1
          rcases hx1 with ⟨x, rfl⟩
          rw [show x + x = 2 * x by omega] at hx ⊢
          ring_nf at hx
          replace hx : x ≤ 2 ^ k:= by omega
          replace ih:= ih x hx (show f x = f x by simp)
          rw [h2 x]
          have g0 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1:= by
            ring_nf
            have h4 : 2 ^ k > 0:= by positivity
            omega
          rw [g0]
          rw [h3 (2 ^ k - 1)]
          omega

  -- Prove the recurrence relation for f(2^(k+1) - 1)
  have h5 : ∀ k : ℕ, f (2 ^ (k + 1) - 1) = 2 ^ k - 1 + 2 * f (2 ^ k - 1):= by
    intro k
    have g0 : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1:= by
      ring_nf
      have h4 : 2 ^ k > 0:= by positivity
      omega
    rw [g0]
    rw [h3 (2 ^ k - 1)]

  -- Prove the closed formula: f(2^k - 1) = k * 2^(k-1) + 1 - 2^k
  replace h5 : ∀ k : ℕ, f (2 ^ k - 1) = k * 2 ^ (k - 1) + 1 - 2 ^ k:= by
    intro k
    suffices f (2 ^ k - 1) + 2 ^ k = k * 2 ^ (k - 1) + 1 by omega
    induction k with
    | zero =>
      simp [h1]
    | succ k ih =>
      replace h5:= h5 k
      have g : 2 ^ k > 0:= by positivity
      rw [h5]
      rw [show k + 1 - 1 = k by omega]
      replace ih : 2 * (f (2 ^ k - 1) + 2 ^ k) = 2 * (k * 2 ^ (k - 1) + 1):= by rw [ih]
      rw [show 2 * (k * 2 ^ (k - 1) + 1) = k * 2 ^ (k - 1 + 1) + 2 by ring] at ih
      by_cases hk : k = 0
      .
        subst k
        simp [h1]
      .
        rw [show k - 1 + 1 = k by omega] at ih
        rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
        rw [show 2 ^ k - 1 + 2 * f (2 ^ k - 1) + 2 * 2 ^ k = 2 * f (2 ^ k - 1) + 2 * 2 ^ k + 2 ^ k - 1 by omega]
        suffices 2 * f (2 ^ k - 1) + 2 * 2 ^ k + 2 ^ k = (k + 1) * 2 ^ k + 1 + 1 by omega
        linarith

  -- Final step: Combine the results to prove the maximum value formula
  intro k
  replace h5:= h5 k
  replace h4:= h4 k
  rw [h5] at h4
  exact h4
