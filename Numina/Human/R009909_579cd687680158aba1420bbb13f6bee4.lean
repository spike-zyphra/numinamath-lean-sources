import Mathlib

/- An infinite sequence $a_{1}, a_{2}, \ldots$ of positive integers is such that $a_{n} \geq 2$ and $a_{n+2}$ divides $a_{n+1}+a_{n}$ for all $n \geq 1$. Prove that there exists a prime which divides infinitely many terms of the sequence. -/
theorem number_theory_605273 (a : ℕ → ℕ)
    (ha : ∀ n, a n ≥ 2) (hdiv : ∀ n, a (n + 2) ∣ a (n + 1) + a n) :
    ∃ p, Nat.Prime p ∧ {n | p ∣ a n}.Infinite := by

  -- We prove by contradiction
  by_contra h
  push_neg at h
  -- Suppose that for all prime p, p divides only finitely many terms of the sequence.
  replace h : ∀ p, Nat.Prime p → {n | p ∣ a n}.Finite := by
    intro p
    obtain hp := h p
    rw [Set.not_infinite] at hp
    exact hp

  -- Then there exists M such that all terms of the sequence are at most M.
  have bounded : ∃ M, ∀ n, a n ≤ M := by
    specialize h 2 Nat.prime_two
    -- By assumption, the prime 2 divides only finitely many terms of the sequence.
    -- Hence, there exists N such that term N and beyond is not divisible by 2.
    have : ∃ N, ∀ n ≥ N, ¬2 ∣ a n := by
      let hF := h.toFinset
      by_cases g : hF.Nonempty
      . use (hF.max' g + 1)
        intro n hn
        by_contra foo
        have : n ∈ hF := by exact (Set.Finite.mem_toFinset h).mpr foo
        have : n ≤ hF.max' g := by exact Finset.le_max' hF n this
        omega
      . simp at g
        use 1
        intro n hn
        by_contra foo
        have : n ∈ hF := by exact (Set.Finite.mem_toFinset h).mpr foo
        rw [g] at this
        simp at this
    obtain ⟨ N, hN ⟩ := this
    -- We show the intermediate result that there exists M' such that
    -- term N and beyond is at most M'.
    have : ∃ M', ∀ k, a (k + N) ≤ M' := by
      set M' := max (a N) (a (N + 1))
      use M'
      -- The prove is by two-step induction on k that term k + N and beyond
      -- is at most M'
      intro k
      induction k using Nat.twoStepInduction with
      | zero => simp [M']
      | one => simp only [M']; ring_nf; simp
      | more k' ih1 ih2 =>
          -- Suppose that term k' + N and term k' + 1 + N are at most M'
          specialize hdiv (k' + N)
          -- Then term k' + N + 2 is less than the sum of term k' + N and term k' + 1 + N
          have  : a (k' + N + 2) < a (k' + N + 1) + a (k' + N) := by
            -- Since term k' + N + 2 divides the sum of term k' + N and term k' + 1 + N,
            -- it is at most that sum. But it cannot equal that sum since
            -- both term k' + N and term k' + 1 + N are Odd and so their sum is even.
            -- But term k' + 2 + N must also be odd. This is impossible.
            rw [lt_iff_le_and_ne]
            constructor
            . apply Nat.le_of_dvd
              . apply Nat.add_pos_left; exact Nat.zero_lt_of_lt (ha (k' + N + 1))
              . exact hdiv
            . have : Even (a (k' + N + 1) + a (k' + N)) := by
                have t1 : Odd (a (k' + N + 1)) := by
                  specialize hN (k' + N + 1) (by linarith)
                  simp at hN
                  exact Nat.odd_iff.mpr hN
                have t2 : Odd (a (k' + N)) := by
                  specialize hN (k' + N) (by linarith)
                  simp at hN
                  exact Nat.odd_iff.mpr hN
                exact Odd.add_odd t1 t2
              by_contra g
              rw [← g] at this
              specialize hN (k' + N + 2) (by linarith)
              revert hN
              simp
              exact Nat.even_iff.mp this

          -- In fact, twice term k' + N + 2 is less than the sum of term k' + N and term k' + 1 + N
          have ineq : a (k' + N + 2) * 2 ≤ a (k' + N + 1) + a (k' + N) := by
            have : ∃ d, d ≥ 2 ∧ a (k' + N + 2) * d = a (k' + N + 1) + a (k' + N) := by
              obtain ⟨ d, hd ⟩ := hdiv
              use d
              constructor
              . by_contra g
                simp at g
                nlinarith
              . exact id (Eq.symm hd)
            obtain ⟨ d, hd ⟩ := this
            calc
              _ ≤ (a (k' + N + 2)) * d := by
                    apply Nat.mul_le_mul_left
                    exact hd.left
              _ = _ := by omega

          -- But by induction hypothesis,  term k' + N and term k' + 1 + N are both at most M'.
          -- Hence, term k' + N + 2 is at most M'
          ring_nf at ineq ih1 ih2 ⊢
          linarith

    obtain ⟨ M', hM' ⟩ := this
    -- Let M'' be the maximum over terms 0 to N - 1.
    have : ∃ M'', ∀ k < N, a k ≤ M'' := by
      by_cases g : N < 1
      . simp at g
        rw [g]
        simp
      . simp at g
        let s := (Finset.range N).image a
        have : s.Nonempty := by simp [s]; exact g
        use (s.max' this)
        intro k hk
        have : a k ∈ s := by apply Finset.mem_image_of_mem a
                             exact Finset.mem_range.mpr hk
        exact Finset.le_max' s (a k) this
    obtain ⟨ M'', hM'' ⟩ := this

    -- We can then take M to be the maximum of M' and M''.
    use max M' M''
    intro n
    by_cases hn : n < N
    . exact le_sup_of_le_right (hM'' n hn)
    . specialize hM' (n - N)
      have : n - N + N = n := by refine Nat.sub_add_cancel ?_; exact Nat.le_of_not_lt hn
      rw [this] at hM'
      exact le_sup_of_le_left hM'

  obtain ⟨ M, hM ⟩ := bounded

  let f : Fin (M + 1) → Set ℕ := fun p ↦ if Nat.Prime p then {n | p.val ∣ a n} else {}

  have claim1 : (⋃ i : Fin (M + 1), f i).Finite := by
    apply Set.finite_iUnion
    intro p
    simp [f]
    by_cases hp : Nat.Prime p
    . simp [hp, h p hp]
    . simp [hp]

  have claim2 : (⋃ i : Fin (M + 1), f i) = (Set.univ : Set ℕ) := by
    ext n
    constructor
    . intro hn; trivial
    . -- for any n, we can find a p s.t. p ∣ a n.
      intro hn
      specialize ha n
      have : ∃ q, Nat.Prime q ∧ q ∣ a n := by
        use (a n).minFac
        constructor
        . refine Nat.minFac_prime ?_; exact Ne.symm (Nat.ne_of_lt ha)
        . exact Nat.minFac_dvd (a n)
      obtain ⟨ q, ⟨ hqp, hqdvd ⟩ ⟩ := this
      have : q ≤ M := by
        calc
          _ ≤ a n := by apply Nat.le_of_dvd
                        . exact Nat.zero_lt_of_lt ha
                        . exact hqdvd
          _ ≤ M := by exact hM n
      let s := f ⟨ q, by omega ⟩

      have : n ∈ s := by simp [s]
                         unfold f
                         simp
                         exact And.symm ⟨hqdvd, hqp⟩
      apply Set.mem_iUnion_of_mem ⟨ q, by omega ⟩
      exact this

  have claim3 : ¬(Set.univ : Set ℕ).Finite := by
    apply Set.infinite_of_injective_forall_mem Nat.succ_injective
    simp [Nat.succ_le_iff]

  rw [← claim2] at claim3
  trivial
