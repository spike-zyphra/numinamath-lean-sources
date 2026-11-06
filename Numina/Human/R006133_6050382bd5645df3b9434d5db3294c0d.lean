import Mathlib
/- Determine all $n \in \mathbb{N}$ such that the expression $n2^{n-1} + 1$ is a perfect square. Consider the case where $0$ is included in the set of natural numbers. -/
theorem number_theory_619596 : {n : ℕ | IsSquare (n * 2 ^ (n - 1) + 1)} = {0, 5}:= by
  -- Extensionality: prove that two sets are equal by showing they have the same elements
  ext n
  constructor
  .
    -- Forward direction: if n is in the set, then n = 0 or n = 5
    intro h
    simp at h
    rcases h with ⟨m, h⟩
    -- Case analysis on whether n = 0
    by_cases hn : n = 0
    .
      -- Case 1: n = 0
      subst n
      simp
    .
      -- Case 2: n ≠ 0, so n > 2
      replace hn : n > 2:= by
        by_contra H
        replace H : n = 1 ∨ n = 2:= by omega
        rcases H with rfl | rfl
        -- Check n = 1: 1*2^0 + 1 = 2, not a perfect square
        simp at h
        replace h : IsSquare 2:= by use m
        absurd h
        native_decide
        -- Check n = 2: 2*2^1 + 1 = 5, not a perfect square
        simp at h
        replace h : IsSquare 5:= by use m
        absurd h
        native_decide
      -- Since n > 2, m must be odd
      have h1 : Odd m:= by
        suffices Odd (m ^ 2) by exact Nat.Odd.of_mul_right this
        ring_nf at h
        use n * 2 ^ (n - 2)
        rw [←h]
        rw [show 2 * (n * 2 ^ (n - 2)) = n * 2 ^ (1 + (n - 2)) by ring]
        rw [show 1 + (n - 2) = n - 1 by omega]
        linarith
      -- Express m as 2k+1 for some k
      rcases h1 with ⟨k, rfl⟩
      replace h : n * 2 ^ (n - 1) = 4 * k * (k + 1):= by linarith
      -- Show that k must be greater than 2
      have hkge : k > 2:= by
        by_contra H
        replace H : k = 0 ∨ k = 1 ∨ k = 2:= by omega
        rcases H with rfl | rfl | rfl
        all_goals
          simp at h
        .
          omega
        all_goals
          -- For k = 0, 1, 2, show that n*2^(n-1) is too large
          have h1 : n ≥ 4:= by
            by_contra H
            replace H : n = 3:= by omega
            subst n
            simp at h
          have h2 : 2 ^ (n - 1) ≥ 2 ^ 3:= by
            replace h1 : n - 1 ≥ 3:= by omega
            refine Nat.pow_le_pow_of_le_right (by omega) h1
          replace h1 : n * 2 ^ (n - 1) ≥ 4 * 2 ^ 3:= by exact Nat.mul_le_mul h1 h2
          linarith
      -- Set m = n - 3 for convenience
      set m:= n - 3 with hm
      clear_value m
      replace hm : n = m + 3:= by omega
      subst n
      rw [show m + 3 - 1 = m + 2 by omega] at h
      rw [show 2 ^ (m + 2) = 4 * 2 ^ m by ring] at h
      replace h : (m + 3) * 2 ^ m = k * (k + 1):= by linarith
      -- Factor m + 3 as 2^t * n where n is odd
      have h1:= Nat.exists_eq_pow_mul_and_not_dvd (show m + 3 ≠ 0 by omega) 2 (by omega)
      rcases h1 with ⟨t, n, h1, h2⟩
      rw [h2] at h
      rw [show 2 ^ t * n * 2 ^ m = n * 2 ^ (t + m) by ring] at h
      -- k and k+1 are coprime
      have g1 : Nat.Coprime k (k + 1):= by simp
      -- Lemma: 2^n ≥ n + 1 for all n
      have h5 : ∀ n : ℕ, 2 ^ n ≥ n + 1:= by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          ring_nf
          linarith
      -- Case analysis on whether k is odd
      by_cases h3 : Odd k
      .
        -- Case 1: k is odd
        replace h3 : Nat.Coprime 2 k:= by exact Nat.coprime_two_left.mpr h3
        replace h3 : Nat.Coprime (2 ^ (t + m)) k:= by exact Nat.Coprime.pow_left (t + m) h3
        have h4 : 2 ^ (t + m) ∣ k * (k + 1):= by use n ; linarith
        replace h4 : 2 ^ (t + m) ∣ k + 1:= by exact Nat.Coprime.dvd_of_dvd_mul_left h3 h4
        rcases h4 with ⟨l, h4⟩
        replace h : k * l = n:= by
          rw [h4] at h
          replace h : 2 ^ (t + m) * n = 2 ^ (t + m) * (k * l):= by linarith
          have g : 2 ^ (t + m) > 0:= by positivity
          exact Eq.symm (Nat.eq_of_mul_eq_mul_left g h)
        -- Show that l = 1
        have h6 : l = 1:= by
          by_contra H
          replace H : l ≥ 2:= by
            by_contra H1
            replace H1 : l = 0:= by omega
            subst l
            simp at h
            subst n
            simp at h2
          replace h : 2 * k ≤ n:= by
            replace H : k * l ≥ k * 2:= by exact Nat.mul_le_mul_left k H
            linarith
          replace H : 2 ^ (t + m) * l ≥ 2 ^ (t + m) * 2:= by exact Nat.mul_le_mul_left (2 ^ (t + m)) H
          rw [show 2 ^ (t + m) * 2 = 2 ^ (t + m + 1) by ring] at H
          rw [←h4] at H
          replace h5:= h5 (t + m + 1)
          replace H : k + 2 ≥ 2 ^ t * n:= by linarith
          have g : 2 ^ t > 0:= by positivity
          replace g : 2 ^ t ≥ 1:= by omega
          replace g : 2 ^ t * n ≥ n:= by exact Nat.le_mul_of_pos_left n g
          linarith
        subst l
        simp at h h4
        subst k
        -- Show that t = 0
        have h6 : t = 0:= by
          by_contra H
          replace H : t ≥ 1:= by omega
          have h6 : 2 ^ t ≥ 2 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) H
          replace h6 : 2 ^ t * n ≥ 2 ^ 1 * n:= by exact Nat.mul_le_mul_right n h6
          simp at h6
          replace h5:= h5 (t + m)
          linarith
        subst t
        simp at h2 h4
        subst n
        ring_nf at h4
        -- Case analysis on m
        by_cases hm : m = 0 ∨ m = 1 ∨ m = 2
        .
          rcases hm with rfl | rfl | rfl
          .
            -- m = 0: leads to n = 3, check if it works
            simp at h4
          .
            -- m = 1: leads to n = 4, check if it works
            simp at h1
          .
            -- m = 2: leads to n = 5, this is our solution
            simp
        .
          -- m ≥ 3: show this leads to contradiction
          replace hm : m ≥ 3:= by omega
          set n:= m - 3 with hn
          clear_value n
          replace hn : m = n + 3:= by omega
          subst m
          ring_nf at h4
          replace h5:= h5 n
          linarith
      .
        -- Case 2: k is even, so k+1 is odd
        simp at h3
        have h4 : Odd (k + 1):= by exact Even.add_one h3
        replace h4 : Nat.Coprime 2 (k + 1):= by exact Nat.coprime_two_left.mpr h4
        replace h4 : Nat.Coprime (2 ^ (t + m)) (k + 1):= by exact Nat.Coprime.pow_left (t + m) h4
        have h6 : 2 ^ (t + m) ∣ k * (k + 1):= by use n ; linarith
        replace h6 : 2 ^ (t + m) ∣ k:= by exact Nat.Coprime.dvd_of_dvd_mul_right h4 h6
        rcases h6 with ⟨l, h6⟩
        replace h : (k + 1) * l = n:= by
          rw [show k * (k + 1) = 2 ^ (t + m) * l * (k + 1) by rw [h6]] at h
          replace h : 2 ^ (t + m) * ((k + 1) * l) = 2 ^ (t + m) * n:= by linarith
          have g : 2 ^ (t + m) > 0:= by positivity
          exact Eq.symm (Nat.eq_of_mul_eq_mul_left g (id (Eq.symm h)))
        -- Show that l = 1
        have h6 : l = 1:= by
          by_contra H
          replace H : l ≥ 2:= by
            by_contra H1
            replace H1 : l = 0:= by omega
            subst l
            simp at h
            subst n
            simp at h5
            linarith
          replace h : (k + 1) * 2 ≤ n:= by
            rw [←h]
            exact Nat.mul_le_mul_left (k + 1) H
          replace H : 2 ^ (t + m) * l ≥ 2 ^ (t + m) * 2:= by exact Nat.mul_le_mul_left (2 ^ (t + m)) H
          rw [show 2 ^ (t + m) * 2 = 2 ^ (t + m + 1) by ring] at H
          replace h5:= h5 (t + m + 1)
          replace h6 : k ≥ t + m + 2:= by linarith
          have g : 2 ^ t > 0:= by positivity
          replace g : 2 ^ t ≥ 1:= by omega
          replace g : 2 ^ t * n ≥ n:= by exact Nat.le_mul_of_pos_left n g
          linarith
        subst l
        simp at h h6
        subst k
        -- Case analysis on t
        by_cases ht : t = 0
        .
          -- t = 0: leads to n = 5 (our solution)
          subst t
          simp at h h2
          subst n
          by_cases hm : m = 0 ∨ m = 1 ∨ m = 2
          .
            rcases hm with rfl | rfl | rfl
            simp at h2
            simp at h2
            simp
          .
            replace hm : m ≥ 3:= by omega
            set n:= m - 3 with hn
            clear_value n
            replace hn : m = n + 3:= by omega
            subst m
            ring_nf at h2
            replace h5:= h5 n
            linarith
        .
          -- t ≥ 1: show this leads to contradiction
          replace ht : t ≥ 1:= by omega
          replace h2 : m + 3 ≥ 2 * n:= by
            replace ht : 2 ^ t ≥ 2 ^ 1:= by exact Nat.pow_le_pow_of_le (h5 1) ht
            replace ht : 2 ^ t * n ≥ 2 ^ 1 * n:= by exact Nat.mul_le_mul_right n ht
            linarith
          replace h5:= h5 (t + m)
          linarith
  .
    -- Reverse direction: if n = 0 or n = 5, then n*2^(n-1) + 1 is a perfect square
    intro h
    simp at h
    rcases h with rfl | rfl
    all_goals
      simp
    -- Verify that 0*2^(-1) + 1 = 1 and 5*2^4 + 1 = 81 are perfect squares
    native_decide
