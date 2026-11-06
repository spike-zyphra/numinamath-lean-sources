import Mathlib
/- Let $N$ be a positive integer. Determine the number of integers $i$ in the set $\{1, 2, \ldots, N\}$ such that the last digit of the product $i(i+1)$ is zero. Show that this number is equal to $\lfloor N/5 \rfloor + \lfloor (N+1)/5 \rfloor$. -/
theorem number_theory_637472 (n : ℕ) (hn : n > 0) : {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ (10 ∣ k * (k + 1))}.ncard = n / 5 + (n + 1) / 5:= by
  -- First case: handle small values n ≤ 3
  by_cases hn : n ≤ 3
  .
    -- For n ≤ 3, prove that no numbers in [1,n] satisfy k(k+1) being divisible by 10
    have g1 : {k | 1 ≤ k ∧ k ≤ n ∧ (10 ∣ k * (k + 1))} = ∅:= by
      ext x
      constructor
      .
        -- Prove that no number x in [1,3] can make x(x+1) divisible by 10
        intro h
        simp at h
        rcases h with ⟨h1, h2⟩
        rcases h2 with ⟨h3, h4⟩
        replace h3 : x = 1 ∨ x = 2 ∨ x = 3:= by omega
        rcases h3 with h3 | h3 | h3
        all_goals
          subst x
          omega
      .
        -- Empty set has no elements
        intro h
        simp at h
    rw [g1]
    -- Handle the three possible cases: n = 1, 2, or 3
    replace hn : n = 1 ∨ n = 2 ∨ n = 3:= by omega
    rcases hn with hn | hn | hn
    all_goals
      subst n
      norm_num
  .
    -- Main case: handle n > 3
    -- Let m = n - 4 to use induction
    set m:= n - 4 with hm
    clear_value m
    replace hm : n = m + 4:= by omega
    subst n
    clear hn
    rw [show m + 4 + 1 = m + 5 by omega]
    clear hn

    -- Prove by induction on m
    induction m with
    -- Base case: m = 0 (n = 4)
    | zero =>
      simp
      use 4
      ext x
      constructor
      .
        -- Prove that 4 is the only number making x(x+1) divisible by 10
        intro h
        simp at h
        rcases h with ⟨h1, h2, h3⟩
        simp
        by_contra H
        replace H : x = 1 ∨ x = 2 ∨ x = 3:= by omega
        rcases H with H | H | H
        all_goals
          subst x
          omega
      .
        intro h
        simp at h
        subst x
        simp
        omega

    -- Inductive step: prove for m + 1 given it holds for m
    | succ m ih =>
      -- Key lemma: k(k+1) is divisible by 10 if and only if k or k+1 is divisible by 5
      have h1 : ∀ k : ℕ, 10 ∣ k * (k + 1) ↔ 5 ∣ k ∨ 5 ∣ k + 1:= by
        intro k
        constructor
        .
          -- If 10 divides k(k+1), then 5 divides k(k+1)
          intro h
          have g : 5 ∣ 10:= by omega
          replace h : 5 ∣ k * (k + 1):= by exact Nat.dvd_trans g h
          replace g : Nat.Prime 5:= by decide
          exact (Nat.Prime.dvd_mul g).mp h
        .
          -- If 5 divides k or k+1, then 10 divides k(k+1)
          intro h
          have h1 : 2 ∣ k * (k + 1):= by
            by_cases h1 : Odd k
            .
              suffices 2 ∣ k + 1 by exact Dvd.dvd.mul_left this k
              have g : Odd 1:= by simp
              suffices Even (k + 1) by exact even_iff_two_dvd.mp this
              exact Odd.add_odd h1 g
            .
              simp at h1
              replace h1 : 2 ∣ k:= by exact even_iff_two_dvd.mp h1
              exact Dvd.dvd.mul_right h1 (k + 1)
          rw [show 10 = 2 * 5 by omega]
          replace h : 5 ∣ k * (k + 1):= by
            rcases h with h | h
            .
              exact Dvd.dvd.mul_right h (k + 1)
            .
              exact Dvd.dvd.mul_left h k
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h1 h

      -- Split into two cases based on whether m+5 is divisible by 10
      by_cases h : 10 ∣ (m + 1 + 4) * (m + 1 + 4 + 1)
      .
        -- Case where m+5 makes the product divisible by 10
        have h0:= h
        replace h:= (h1 (m + 1 + 4)).1 h
        -- Prove finiteness of the set for both m and m+1
        have h2 : ∀ m : ℕ, Finite {k | 1 ≤ k ∧ k ≤ m + 4 ∧ 10 ∣ k * (k + 1)}:= by
          intro m
          have h2 : {k | 1 ≤ k ∧ k ≤ m + 4 ∧ 10 ∣ k * (k + 1)} ⊆ Finset.range (m + 5):= by
            intro x h
            simp at h
            replace h:= h.2.1
            simp
            omega
          have h3 : Finite (↑(Finset.range (m + 5)) : Set ℕ):= by exact Finite.of_fintype ↑↑(Finset.range (m + 5))
          exact Finite.Set.subset (↑(Finset.range (m + 5))) h2
        have h3:= h2 (m + 1)
        replace h2:= h2 m
        have h4:= Set.Finite.exists_finset_coe h2
        have h5:= Set.Finite.exists_finset_coe h3
        rcases h4 with ⟨A, h4⟩
        rcases h5 with ⟨B, h5⟩
        rw [←h4] at ih
        rw [←h5]
        rw [Set.ncard_coe_Finset] at ih ⊢

        -- Prove B is A with m+5 inserted
        have h6 : B = insert (m + 1 + 4) A:= by
          rw [Finset.insert_eq (m + 1 + 4) A]
          ext x
          constructor
          .
            intro h
            simp at h
            replace h : x ∈ (↑B : Set ℕ):= by exact h
            rw [h5] at h
            simp at h
            by_cases hx : x = m + 1 + 4
            .
              subst x
              simp
            .
              rcases h with ⟨h1, h2, h3⟩
              replace h2 : x ≤ m + 4:= by omega
              simp
              right
              suffices x ∈ (↑A : Set ℕ) by exact this
              rw [h4]
              simp
              exact ⟨h1, h2, h3⟩
          .
            intro h
            simp at h
            rcases h with h | h
            .
              suffices x ∈ (↑B : Set ℕ) by exact this
              rw [h5]
              subst x
              simp
              exact h0
            .
              replace h : x ∈ (↑A : Set ℕ):= by exact h
              suffices x ∈ (↑B : Set ℕ) by exact this
              rw [h4] at h
              rw [h5]
              simp at h
              simp
              rcases h with ⟨h1, h2, h3⟩
              replace h2 : x ≤ m + 1 + 4:= by omega
              exact ⟨h1, h2, h3⟩
        rw [h6]
        rw [Finset.card_insert_of_not_mem]
        .
          -- Complete the proof using the inductive hypothesis
          rw [ih]
          rcases h with h | h
          .
            ring_nf at h
            replace h : 5 ∣ m:= by exact Nat.dvd_add_self_left.mp h
            rcases h with ⟨k, h⟩
            subst m
            omega
          .
            rw [show m + 1 + 4 + 1 = m + 1 + 5 by omega]
            replace h : 5 ∣ m + 1:= by exact Nat.dvd_add_self_right.mp h
            rcases h with ⟨k, h⟩
            rw [show m + 4 = 5 * k + 3 by omega]
            rw [show m + 5 = 5 * k + 4 by omega]
            rw [show m + 1 + 5 = 5 * k + 5 by omega]
            omega
        .
          -- Prove m+5 is not in set A
          by_contra H
          replace H : m + 1 + 4 ∈ (↑A : Set ℕ):= by exact H
          rw [h4] at H
          simp at H
      .
        -- Case where m+5 does not make the product divisible by 10
        have h2 : {k | 1 ≤ k ∧ k ≤ m + 1 + 4 ∧ 10 ∣ k * (k + 1)} = {k | 1 ≤ k ∧ k ≤ m + 4 ∧ 10 ∣ k * (k + 1)}:= by
          ext x
          constructor
          .
            intro h2
            simp at h2
            replace h : x ≠ m + 1 + 4:= by
              by_contra H
              subst x
              replace h2:= h2.2.2
              trivial
            rcases h2 with ⟨h2, h3, h4⟩
            replace h3 : x ≤ m + 4:= by omega
            simp
            exact ⟨h2, h3, h4⟩
          .
            intro h2
            simp at h
            rcases h2 with ⟨h2, h3, h4⟩
            exact ⟨h2, (by omega), h4⟩
        rw [h2, ih]
        -- Complete proof using modular arithmetic
        replace h1 : m + 1 + 4 ≡ 1 [MOD 5] ∨ m + 1 + 4 ≡ 2 [MOD 5] ∨ m + 1 + 4 ≡ 3 [MOD 5]:= by
          set t:= m + 1 + 4 with ht
          clear_value t
          mod_cases t % 5
          any_goals
            tauto
          .
            replace H : 5 ∣ t:= by exact Nat.dvd_of_mod_eq_zero H
            replace h1:= (h1 t).2 (by left ; exact H)
            trivial
          .
            replace H : t + 1 ≡ 4 + 1 [MOD 5]:= by exact Nat.ModEq.add_right 1 H
            simp at H
            replace H : 5 ∣ t + 1:= by exact Nat.dvd_of_mod_eq_zero H
            replace h1:= (h1 t).2 (by right ; exact H)
            trivial
        rcases h1 with h1 | h1 | h1
        .
          -- Case: m+5 ≡ 1 (mod 5)
          replace h1 : 5 ∣ m + 4 + 1 - 1:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))
          norm_num at h1
          rcases h1 with ⟨k, h1⟩
          rw [h1, show m + 5 = 5 * k + 1 by omega, show m + 1 + 5 = 5 * k + 2 by omega]
          omega
        .
          -- Case: m+5 ≡ 2 (mod 5)
          replace h1 : 5 ∣ m + 4 + 1 - 2:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))
          rw [show m + 4 + 1 - 2 = m + 3 by omega] at h1
          rcases h1 with ⟨k, h1⟩
          rw [show m + 4 = 5 * k + 1 by omega, show m + 5 = 5 * k + 2 by omega, show m + 1 + 5 = 5 * k + 3 by omega]
          omega
        .
          -- Case: m+5 ≡ 3 (mod 5)
          replace h1 : 5 ∣ m + 4 + 1 - 3:= by exact (Nat.modEq_iff_dvd' (by omega)).mp (id (Nat.ModEq.symm h1))
          rw [show m + 4 + 1 - 3 = m + 2 by omega] at h1
          rcases h1 with ⟨k, h1⟩
          rw [show m + 4 = 5 * k + 2 by omega, show m + 5 = 5 * k + 3 by omega, show m + 1 + 5 = 5 * k + 4 by omega]
          omega
