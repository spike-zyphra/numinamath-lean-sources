import Mathlib
/- USA   Suppose that $s_{1}, s_{2}, s_{3}, \ldots$ is a strictly increasing sequence of positive integers such that the subsequences  $$ s_{s_{1}}, s_{s_{2}}, s_{s_{3}}, \ldots \quad \text { and } \quad s_{s_{1}+1}, s_{s_{2}+1}, s_{s_{3}+1}, \ldots $$  are both arithmetic progressions. Prove that $s_{1}, s_{2}, s_{3}, \ldots$ is itself an arithmetic progression. -/
theorem algebra_23808 (s : ℕ → ℕ) (hpos : ∀ n, 0 < s n) (hinc : StrictMono s) (hs : ∃ (a d : ℕ), ∀ n, s (s n) = a + d * n)
    (hs' : ∃ (a d : ℕ), ∀ n, s (s n + 1) = a + d * n) : ∃ (a d : ℕ), ∀ n, s n = a + d * n := by
    -- Extract the parameters of the first arithmetic progression
    rcases hs with ⟨a1, d1, h1⟩
    -- Extract the parameters of the second arithmetic progression
    rcases hs' with ⟨a2, d2, h2⟩
    -- Define the difference function d(n) = s(n+1) - s(n)
    set d : ℕ → ℕ := fun n => s (n + 1) - s n with hd
    clear_value d
    -- Prove that the difference between s(m) and s(n) is at least m-n when m > n
    have h3 : ∀ n m : ℕ, m > n → s m - s n ≥ m - n:= by
        intro n m hm
        induction m, hm using Nat.le_induction with
        | base =>
            simp
            simp [StrictMono] at hinc
            specialize hinc (show n < n + 1 by omega)
            omega
        | succ m hm ih =>
            simp
            simp at hm
            simp [StrictMono] at hinc
            specialize hinc (show m < m + 1 by omega)
            omega
    -- Prove that the difference function d is bounded above by d1
    have h4 : ∃ D : ℕ, ∀ n : ℕ, d n ≤ D:= by
        use d1
        intro n
        simp [hd]
        have g1:= h1 (n + 1)
        have g2:= h1 n
        simp [StrictMono] at hinc
        specialize h3 (s n) (s (n + 1)) (show s (n + 1) > s n by exact hinc (show n < n + 1 by omega))
        rw [g1, g2] at h3
        have g3 : a1 + d1 * (n + 1) = (a1 + d1 * n) + d1:= by ring
        rw [show a1 + d1 * (n + 1) - (a1 + d1 * n) = d1 by omega] at h3
        simp at h3
        exact h3
    -- Extract the upper bound D
    rcases h4 with ⟨D, hD⟩
    -- Define the set S of all values of the difference function
    set S:= {d n | n : ℕ} with hS
    clear_value S
    -- Prove that S is bounded above
    have h4 : BddAbove S:= by
        simp [BddAbove]
        have h5 : D ∈ upperBounds S:= by
            simp [upperBounds]
            intro x hx
            subst S
            simp at hx
            rcases hx with ⟨n, hn⟩
            rw [←hn]
            exact hD n
        exact Set.nonempty_of_mem h5
    -- Prove that S is bounded below by 1
    have h5 : BddBelow S:= by
        simp [BddBelow]
        have h5 : 1 ∈ lowerBounds S:= by
            simp [lowerBounds]
            intro x hx
            subst S
            simp at hx
            rcases hx with ⟨n, hn⟩
            rw [←hn]
            simp [hd]
            simp [StrictMono] at hinc
            specialize hinc (show n < n + 1 by omega)
            omega
        exact Set.nonempty_of_mem h5
    -- Prove that S is nonempty
    have h6 : S.Nonempty:= by
        have h6 : d 1 ∈ S:= by
            subst S
            simp
        exact Set.nonempty_of_mem h6
    -- Get the maximum element of S
    have h7:= BddAbove.exists_isGreatest_of_nonempty h4 h6
    -- Get the minimum element of S
    have h8:= BddBelow.exists_isLeast_of_nonempty h5 h6
    rcases h7 with ⟨M, hM⟩
    rcases h8 with ⟨m, hm⟩
    clear h4 h5 h6
    -- Case analysis: either the maximum equals the minimum, or not
    by_cases h : M = m
    -- Case 1: M = m, meaning all differences are equal
    .
        subst M
        rcases hm with ⟨hm1, hm2⟩
        rcases hM with ⟨hM1, hM2⟩
        clear hm1 hM1
        simp [lowerBounds] at hm2
        simp [upperBounds] at hM2
        -- Prove that all differences are equal to m
        have h4 : ∀ n : ℕ, d n = m:= by
            intro n
            specialize hm2 (show d n ∈ S by subst S; simp)
            specialize hM2 (show d n ∈ S by subst S; simp)
            linarith
        -- Conclude that s is an arithmetic progression with common difference m
        use (s 0), m
        intro n
        induction n with
        | zero =>
            simp
        | succ n ih =>
            specialize h4 n
            simp [hd] at h4
            simp [StrictMono] at hinc
            specialize hinc (show n < n + 1 by omega)
            rw [show s (n + 1) = s (n + 1) - s n + s n by omega]
            rw [h4, ih]
            linarith
    -- Case 2: M ≠ m, meaning the differences are not all equal
    .
        -- Prove that the differences of differences form an arithmetic sequence
        replace h2 : ∃ d3 : ℝ, ∀ n : ℕ, ↑(d (s (n + 1)) : ℝ) - ↑(d (s n) : ℝ) = d3:= by
            have g1 : ∀ n : ℕ, s (s (n + 1) + 1) - s (s n + 1) = d2:= by
                intro n
                simp [h2]
                suffices a2 + d2 * (n + 1) = (a2 + d2 * n) + d2 by omega
                linarith
            have g2 : ∀ n : ℕ, s (s (n + 1)) - s (s n) = d1:= by
                intro n
                simp [h1]
                suffices a1 + d1 * (n + 1) = (a1 + d1 * n) + d1 by omega
                linarith
            use ((↑d2 : ℝ) - ↑d1)
            intro n
            simp [StrictMono] at hinc
            have g3:= hinc (show s n < s (n + 1) by exact hinc (show n < n + 1 by omega))
            have g4:= hinc (show s n + 1 < s (n + 1) + 1 by linarith [hinc (show n < n + 1 by omega)])
            specialize g1 n
            specialize g2 n
            replace g1 : s (s (n + 1) + 1) = s (s n + 1) + d2:= by omega
            replace g2 : s (s (n + 1)) = s (s n) + d1:= by omega
            have g5 : s (s (n + 1) + 1) = s (s (n + 1)) + d (s (n + 1)):= by
                simp [hd]
                specialize hinc (show s (n + 1) < s (n + 1) + 1 by omega)
                omega
            have g6 : s (s n + 1) = s (s n) + d (s n):= by
                simp [hd]
                specialize hinc (show s n < s n + 1 by omega)
                omega
            rw [g5, g6, g2] at g1
            replace g1 : d1 + d (s (n + 1)) = d (s n) + d2:= by omega
            rify at g1
            clear g2 g3 g4 g5 g6
            linarith
        -- Simplify the expression for the first arithmetic progression
        replace h1 : ∀ n : ℕ, s (s (n + 1)) - s (s n) = d1:= by
            intro n
            simp [h1]
            suffices a1 + d1 * (n + 1) = (a1 + d1 * n) + d1 by omega
            linarith
        rcases h2 with ⟨d3, h2⟩
        rcases hm with ⟨hm1, hm2⟩
        rcases hM with ⟨hM1, hM2⟩
        -- Confirm that M > m
        replace h : M > m:= by
            simp [lowerBounds] at hm2
            specialize hM2 hm1
            omega
        rw [hS] at hm1 hM1
        simp at hm1 hM1
        rcases hm1 with ⟨n1, hn1⟩
        rcases hM1 with ⟨n2, hn2⟩
        -- Prove that m is positive
        have hmpos : m > 0:= by
            rw [←hn1]
            simp [hd]
            linarith [hinc (show n1 < n1 + 1 by omega)]
        simp [StrictMono] at hinc
        -- Prove a formula for sums of consecutive differences
        have h4 : ∀ m n : ℕ, ∑ i ∈ Finset.range m, d (n + i) = s (n + m) - s n:= by
            intro m n
            induction m with
            | zero =>
                simp [hd]
            | succ m ih =>
                rw [Finset.sum_range_succ, ih]
                simp [hd]
                have g1:= hinc (show n + m < n + m + 1 by omega)
                by_cases hm : m = 0
                .
                    subst m
                    simp
                .
                    have g2:= hinc (show n < n + m by omega)
                    rw [show n + (m + 1) = n + m + 1 by omega]
                    omega
        -- Prove key properties about the relationship between m and M
        have h5 : (∀ n : ℕ, d n = m → d (s n) = M) ∧ (∀ n : ℕ, d n = M → d (s n) = m):= by
            have h5 : d1 = M * m:= by
                have h5 : d1 ≤ M * m:= by
                    rw [←(h1 n1)]
                    simp [hd] at hn1
                    replace hn1 : s (n1 + 1) = s n1 + m:= by
                        specialize hinc (show n1 < n1 + 1 by omega)
                        omega
                    rw [hn1]
                    rw [←h4 m (s n1)]
                    have g1 : ∀ i : ℕ, i ∈ Finset.range m → d (s n1 + i) ≤ M:= by
                        intro i _
                        simp [upperBounds] at hM2
                        exact hM2 (show d (s n1 + i) ∈ S by subst S; simp)
                    replace g1 : ∑ i ∈ Finset.range m, d (s n1 + i) ≤ ∑ _ ∈ Finset.range m, M:= by exact Finset.sum_le_sum g1
                    simp at g1
                    linarith only [g1]
                have h5 : d1 ≥ M * m:= by
                    rw [←(h1 n2)]
                    simp [hd] at hn2
                    replace hn2 : s (n2 + 1) = s n2 + M:= by
                        specialize hinc (show n2 < n2 + 1 by omega)
                        omega
                    rw [hn2]
                    rw [←h4 M (s n2)]
                    have g1 : ∀ i : ℕ, i ∈ Finset.range M → d (s n2 + i) ≥ m:= by
                        intro i _
                        simp [lowerBounds] at hm2
                        exact hm2 (show d (s n2 + i) ∈ S by subst S; simp)
                    replace g1 : ∑ i ∈ Finset.range M, d (s n2 + i) ≥ ∑ _ ∈ Finset.range M, m:= by exact Finset.sum_le_sum g1
                    simp at g1
                    linarith only [g1]
                omega
            constructor
            -- Prove that if d(n) = m, then d(s(n)) = M
            .
                intro n hn
                specialize h4 m (s n)
                have g1 : s n + m = s (n + 1):= by
                    rw [←hn]
                    simp [hd]
                    specialize hinc (show n < n + 1 by omega)
                    rw [show s n + (s (n + 1) - s n) = (s (n + 1) - s n) + s n by omega]
                    omega
                rw [g1] at h4
                clear g1
                rw [h1 n, h5] at h4
                have h6 : ∀ i : ℕ, i ∈ Finset.range m → d (s n + i) ≤ M:= by
                    intro i _
                    simp [upperBounds] at hM2
                    exact hM2 (show d (s n + i) ∈ S by subst S; simp)
                rw [show M * m = ∑ _ ∈ Finset.range m, M by simp ; ring] at h4
                set f:= fun i : ℕ => d (s n + i) with hf
                set g:= fun _ : ℕ => M with hg
                clear_value f g
                replace h6 : ∀ i ∈ Finset.range m, f i ≤ g i:= by
                    simp [hf, hg]
                    simp at h6
                    exact h6

                replace h4:= (Finset.sum_eq_sum_iff_of_le h6).1 h4
                simp [hf, hg] at h4
                specialize h4 0 (by omega)
                simp at h4
                exact h4
            -- Prove that if d(n) = M, then d(s(n)) = m
            .
                intro n hn
                specialize h4 M (s n)
                have g1 : s n + M = s (n + 1):= by
                    rw [←hn]
                    simp [hd]
                    specialize hinc (show n < n + 1 by omega)
                    rw [show s n + (s (n + 1) - s n) = (s (n + 1) - s n) + s n by omega]
                    omega
                rw [g1] at h4
                clear g1
                rw [h1 n, h5] at h4
                have h6 : ∀ i : ℕ, i ∈ Finset.range M → d (s n + i) ≥ m:= by
                    intro i _
                    simp [lowerBounds] at hm2
                    exact hm2 (show d (s n + i) ∈ S by subst S; simp)
                rw [show M * m = ∑ _ ∈ Finset.range M, m by simp] at h4
                set f:= fun i : ℕ => d (s n + i) with hf
                set g:= fun _ : ℕ => m with hg
                clear_value f g
                replace h6 : ∀ i ∈ Finset.range M, f i ≥ g i:= by
                    simp [hf, hg]
                    simp at h6
                    exact h6
                replace h4:= (Finset.sum_eq_sum_iff_of_le h6).1 (by simp [h4])
                simp [hf, hg] at h4
                specialize h4 0 (by omega)
                simp at h4
                rw [h4]
        rcases h5 with ⟨h5, h6⟩
        clear h4 hmpos hm2 hM2 h1 hS S hD D hd a1 a2 d2 d1
        -- Apply the key properties to specific values
        have g1:= h5 n1 hn1
        have g2:= h6 n2 hn2
        have g3:= h5 (s n2) g2
        have g4:= h6 (s n1) g1
        -- Prove that s(n) > n for specific values
        have g5 : s n2 > n2:= by
            by_cases hn2 : n2 = 0
            .
                subst n2
                exact hpos 0
            .
                specialize h3 0 n2 (by omega)
                specialize hpos 0
                omega
        have g6 : s n1 > n1:= by
            by_cases hn1 : n1 = 0
            .
                subst n1
                exact hpos 0
            .
                specialize h3 0 n1 (by omega)
                specialize hpos 0
                omega
        -- Extend the property of differences to arbitrary indices
        replace h2 : ∀ n m : ℕ, m > n → (↑(d (s m)) : ℝ) - d (s n) = d3 * (m - n):= by
            intro n m hm
            induction m, hm using Nat.le_induction with
            | base =>
                simp
                exact h2 n
            | succ m hm ih =>
                simp
                simp at hm
                specialize h2 m
                linarith
        -- Case analysis on the sign of d3
        by_cases hd3 : d3 ≥ 0
        -- Case 2a: d3 ≥ 0
        .
            replace h2 : ∀ m n : ℕ, m > n → d (s m) ≥ d (s n):= by
                intro m n hm
                rify
                specialize h2 n m hm
                rify at hm
                replace hm : ((↑m : ℝ) - n) ≥ 0:= by linarith
                replace hm : d3 * ((↑m : ℝ) - n) ≥ 0:= by positivity
                linarith
            replace g6:= h2 (s n1) n1 g6
            linarith
        -- Case 2b: d3 < 0
        .
            replace h2 : ∀ m n : ℕ, m > n → d (s n) ≥ d (s m):= by
                intro m n hm
                rify
                specialize h2 n m hm
                rify at hm
                simp at hd3
                replace hd3 : -d3 ≥ 0:= by linarith
                replace hm : ((↑m : ℝ) - n) ≥ 0:= by linarith
                replace hm : (-d3) * ((↑m : ℝ) - n) ≥ 0:= by positivity
                linarith
            replace g5:= h2 (s n2) n2 g5
            linarith
