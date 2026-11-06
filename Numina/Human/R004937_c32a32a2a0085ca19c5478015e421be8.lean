import Mathlib
/- On dit qu'une suite $\left(u_{n}\right)_{n \geqslant 1}$ est Sicilienne si $u_{1}$ est un entier strictement positif, et si pour tout $n$,

$$
u_{n+1}= \begin{cases}u_{n} / 2 & \text { si } u_{n} \text { est pair, et } \\ u_{n}+\left[\sqrt{u_{n}}\right] & \text { si } u_{n} \text { est impair. }\end{cases}
$$

Existe-t-il une suite Sicilienne $\left(u_{n}\right)_{n \geqslant 1}$ telle que $u_{n}>1$ pour tout $n$ ?
(N.B. $[x]$ désigne la partie entière de $x$. Par exemple, $[2,71828]=2$.) -/
theorem number_theory_604708 (a : ℕ → ℤ) (h1 : a 1 > 0) (h2 : ∀ n : ℕ, n ≥ 1 → (Even (a n) → a (n + 1) = a n / 2) ∧ (Odd (a n) → a (n + 1) = a n + ⌊√(a n)⌋)) (h : ∀ n : ℕ, n ≥ 1 → a n > 1) : False:= by
  -- First, we show that the set of terms a_n for n > 1 has a least element
  have h3 : ∃ m : ℤ, IsLeast {S : ℤ | ∃ n : ℕ, n > 1 ∧ S = a n} m:= by
    -- Use the fact that bounded below non-empty sets have a least element
    refine BddBelow.exists_isLeast_of_nonempty ?_ ?_
    -- Show the set is bounded below by 1
    simp [BddBelow]
    use 1
    simp [lowerBounds]
    intro S n hn hS
    subst S
    replace h:= h n (by omega)
    linarith
    -- Show the set is non-empty by using a_2
    use a 2
    simp
    use 2
    simp
  -- Extract the least element and the index where it occurs
  rcases h3 with ⟨m, hm1, hm2⟩
  simp at hm1
  rcases hm1 with ⟨n, hn, hm1⟩
  subst m
  -- Let M be the least element
  set M:= a n with hM
  clear_value M
  -- Case analysis: M is even or odd
  by_cases g : Even M
  .
    -- Case 1: M is even
    rcases g with ⟨M, rfl⟩
    rw [show M + M = 2 * M by omega] at hm2 hM
    -- Apply the recurrence relation for even numbers
    replace h2:= (h2 n (by omega)).1 (by rw [←hM] ; simp)
    rw [←hM] at h2
    simp at h2
    -- Show that a_{n+1} violates the minimality of M
    simp [lowerBounds] at hm2
    replace hm2:= hm2 (n + 1) (by omega) (show a (n + 1) = a (n + 1) by simp)
    replace h:= h n (by omega)
    linarith
  .
    -- Case 2: M is odd
    simp at g
    -- Let k be the floor of square root of M
    set k:= ⌊√(a n)⌋ with hk
    clear_value k
    have hMpos:= h n (by omega)
    rw [←hM] at hMpos hk
    -- Show that k^2 ≤ M < (k+1)^2
    have hk1 : k ^ 2 ≤ M:= by
      have hk1 : ⌊√(a n)⌋ ≤ √(a n):= by exact Int.floor_le √(a n)
      rw [←hM] at hk1
      rw [←hk] at hk1
      rw [show k = |(↑k : ℝ)| by subst k ; exact Eq.symm (abs_of_nonneg (by positivity))] at hk1
      rw [show √M = |√M| by exact Eq.symm (abs_of_nonneg (by positivity))] at hk1
      replace hk1:= sq_le_sq.mpr hk1
      field_simp at hk1
      rify
      exact hk1
    have hk2 : M < (k + 1) ^ 2:= by
      have hk2 : √M < k + 1:= by
        subst k
        exact Int.lt_floor_add_one √↑M
      rw [show √M = |√M| by exact Eq.symm (abs_of_nonneg (by positivity))] at hk2
      rw [show k + 1 = |(↑k : ℝ) + 1| by subst k ; exact Eq.symm (abs_of_nonneg (by positivity))] at hk2
      replace hk2:= sq_lt_sq.mpr hk2
      field_simp at hk2
      rify
      exact hk2
    have hkpos : k ≥ 0:= by subst k ; positivity
    -- Show that k must be even
    have g3 : Even k:= by
      by_contra g3
      simp at g3
      -- Apply the recurrence relation for odd numbers
      have g2:= (h2 n (by omega)).2 (by rw [←hM] ; exact g)
      rw [←hM] at g2
      rw [←hk] at g2
      -- Show that M + k is even
      replace g3 : Even (M + k):= by exact Odd.add_odd g g3
      have g4:= (h2 (n + 1) (by omega)).1 (by rw [g2] ; exact g3)
      rcases g3 with ⟨t, ht⟩
      rw [show t + t = 2 * t by omega] at ht
      rw [g2, ht] at g4
      simp at g4
      rw [show n + 1 + 1 = n + 2 by omega] at g4
      -- Show that k ≥ M, which leads to a contradiction
      simp [lowerBounds] at hm2
      replace hm2:= hm2 (n + 2) (by omega) (show a (n + 2) = a (n + 2) by simp)
      replace hm2 : k ≥ M:= by linarith
      have hk3 : k ≤ k ^ 2:= by exact Int.le_self_sq k
      replace hm2 : k = M:= by linarith
      rw [hm2] at hk1
      nlinarith only [hk1, hMpos]
    -- Show that M ≤ 3k + 1
    have hk3 : M ≤ 3 * k + 1:= by
      have g2:= (h2 n (by omega)).2 (by rw [←hM] ; exact g)
      rw [←hM] at g2
      rw [←hk] at g2

      -- Case analysis on whether M ≤ k^2 + k
      by_cases g1 : M ≤ k ^ 2 + k
      .
        -- Subcase: M ≤ k^2 + k
        replace g3 : Odd (M + k):= by exact Even.odd_add g3 g
        -- Show that ⌊√(M + k)⌋ = k
        have g4 : ⌊√(M + k)⌋ = k:= by
          refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
          rify at hk
          have g4 : |(k : ℝ)| ≥ k:= by exact le_abs_self (↑k : ℝ)
          rw [show √(M + k) = |√(M + k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices |(k : ℝ)| ≤ |√(M + k)| by linarith
          suffices k ^ 2 ≤ √(M + k) ^ 2 by exact sq_le_sq.mp this
          field_simp
          suffices k ^ 2 ≤ M + k by rify at this ; linarith
          linarith
          rw [show (↑k : ℝ) + 1 = |(↑k : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
          rw [show √(M + k) = |√(M + k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices √(M + k) ^ 2 < (k + 1) ^ 2 by exact sq_lt_sq.mp this
          field_simp
          suffices M + k < (k + 1) ^ 2 by rify at this ; linarith
          linarith
        -- Apply the recurrence relation
        have g5:= (h2 (n + 1) (by omega)).2 (by rw [g2] ; exact g3)
        rw [show n + 1 + 1 = n + 2 by omega] at g5
        rw [g2] at g5
        simp at g5
        rw [g4] at g5
        -- Show that k must be even (contradiction)
        replace g3 : Even k:= by
          by_contra H
          simp at H
          absurd g3
          simp
          exact Odd.add_odd g H
        rw [show M + k + k = M + 2 * k by omega] at g5
        have g6 : Odd (M + 2 * k):= by
          have g6 : Even (2 * k):= by simp
          exact Even.odd_add g6 g
        -- Show that ⌊√(M + 2k)⌋ = k + 1
        have g7 : ⌊√(M + 2 * k)⌋ = k + 1:= by
          have gk : M ≠ k ^ 2:= by
            by_contra H
            rw [H] at g
            absurd g
            simp
            refine (Int.even_pow' (by omega)).mpr g3
          refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
          simp
          rw [show √(↑M + 2 * ↑k) = |√(↑M + 2 * ↑k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          rw [show (k : ℝ) + 1 = |(↑k : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices (k + 1) ^ 2 ≤ √(M + 2 * k) ^ 2 by exact sq_le_sq.mp this
          field_simp
          suffices (k + 1) ^ 2 ≤ M + 2 * k by rify at this ; linarith
          replace hk1 : M > k ^ 2:= by
            by_contra H
            simp at H
            replace H : M = k ^ 2:= by linarith
            trivial
          clear gk
          linarith
          simp
          rw [show (k : ℝ) + 1 + 1 = k + 2 by linarith]
          rw [show √(↑M + 2 * ↑k) = |√(↑M + 2 * ↑k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          rw [show (k : ℝ) + 2 = |(↑k : ℝ) + 2| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices √(M + 2 * k) ^ 2 < (k + 2) ^ 2 by exact sq_lt_sq.mp this
          field_simp
          suffices M + 2 * k < (k + 2) ^ 2 by rify at this ; linarith
          linarith
        -- Continue applying the recurrence relation
        have g8:= (h2 (n + 2) (by omega)).2 (by rw [g5] ; exact g6)
        rw [show n + 2 + 1 = n + 3 by omega] at g8
        rw [g5] at g8
        simp at g8
        rw [g7] at g8
        rw [show M + 2 * k + (k + 1) = M + 3 * k + 1 by omega] at g8
        -- Show that M + 3k + 1 is even
        replace g6 : Even (M + 3 * k + 1):= by
          rcases g with ⟨M1, hM1⟩
          rcases g3 with ⟨k1, hk1⟩
          rw [hM1, hk1]
          use M1 + 3 * k1 + 1
          ring
        rcases g6 with ⟨s, hs⟩
        rw [show s + s = 2 * s by omega] at hs
        -- Apply the recurrence relation for even numbers
        replace h2:= (h2 (n + 3) (by omega)).1 (by rw [g8] ; rw [hs] ; simp)
        rw [g8, hs] at h2
        simp at h2
        rw [show n + 3 + 1 = n + 4 by omega] at h2
        -- Show that this violates the minimality of M
        simp [lowerBounds] at hm2
        replace hm2:= hm2 (n + 4) (by omega) (show a (n + 4) = a (n + 4) by simp)
        linarith
      .
        -- Subcase: M > k^2 + k
        simp at g1 g3
        have g4 : Odd (M + k):= by exact Even.odd_add g3 g
        -- Show that ⌊√(M + k)⌋ = k + 1
        have g5 : ⌊√(M + k)⌋ = k + 1:= by
          refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
          simp
          rw [show √(↑M + ↑k) = |√(↑M + ↑k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          rw [show (k : ℝ) + 1 = |(↑k : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices (k + 1) ^ 2 ≤ √(M + k) ^ 2 by exact sq_le_sq.mp this
          field_simp
          suffices (k + 1) ^ 2 ≤ M + k by rify at this ; linarith
          linarith
          simp
          rw [show (k : ℝ) + 1 + 1 = k + 2 by linarith]
          rw [show √(↑M + ↑k) = |√(↑M + ↑k)| by exact Eq.symm (abs_of_nonneg (by positivity))]
          rw [show (k : ℝ) + 2 = |(↑k : ℝ) + 2| by exact Eq.symm (abs_of_nonneg (by positivity))]
          suffices √(M + k) ^ 2 < (k + 2) ^ 2 by exact sq_lt_sq.mp this
          field_simp
          suffices M + k < (k + 2) ^ 2 by rify at this ; linarith
          linarith
        -- Apply the recurrence relation
        have g6:= (h2 (n + 1) (by omega)).2 (by rw [g2] ; exact g4)
        rw [show n + 1 + 1 = n + 2 by omega] at g6
        rw [g2] at g6
        simp at g6
        rw [g5] at g6
        rw [show M + k + (k + 1) = M + 2 * k + 1 by omega] at g6
        -- Show that M + 2k + 1 is even
        replace g4 : Even (M + 2 * k + 1):= by
          rcases g with ⟨M1, hM1⟩
          rw [hM1]
          use M1 + k + 1
          ring
        -- Apply the recurrence relation for even numbers
        have g7:= (h2 (n + 2) (by omega)).1 (by rw [g6] ; exact g4)
        rw [show n + 2 + 1 = n + 3 by omega] at g7
        rw [g6] at g7
        rcases g4 with ⟨s, hs⟩
        rw [show s + s = 2 * s by omega] at hs
        rw [hs] at g7
        simp at g7
        -- Show that this violates the minimality of M
        simp [lowerBounds] at hm2
        replace hm2:= hm2 (n + 3) (by omega) (show a (n + 3) = a (n + 3) by simp)
        linarith
    -- Show that 3k + 1 ≥ k^2, which implies k < 4
    replace hk3 : 3 * k + 1 ≥ k ^ 2:= by linarith
    have g4 : k ≥ 1:= by
      rw [hk]
      refine Int.le_floor.mpr ?_
      simp
      rify at hMpos
      linarith
    replace hk3 : k < 4:= by
      by_contra H
      simp at H
      have H1 : k * (k - 4) ≥ 0:= by
        replace H : k - 4 ≥ 0:= by linarith
        positivity
      linarith
    -- Since k is even and 1 ≤ k < 4, we have k = 2
    rcases g3 with ⟨k, rfl⟩
    replace hk3 : k = 1:= by linarith
    subst k
    -- Since M is odd and k = 1, we have M = 3
    rcases g with ⟨M, rfl⟩
    norm_num at hk1 hk2
    replace hMpos : M = 2 ∨ M = 3:= by omega
    clear g4 hkpos hk1 hk2 hk
    -- Show that if a_n = 7, then a_{n+4} = 3
    have g : ∀ n : ℕ, n > 1 → a n = 7 → a (n + 4) = 3:= by
      intro n hn g
      -- Apply the recurrence relation for odd numbers
      have g1:= (h2 n (by omega)).2 (by rw [g] ; decide)
      rw [g] at g1
      simp at g1
      -- Show that ⌊√7⌋ = 2
      have g2 : ⌊√7⌋ = 2:= by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        simp
        have g2 : (7 : ℝ) ≥ 2 ^ 2:= by linarith
        replace g2:= Real.sqrt_le_sqrt g2
        field_simp at g2
        exact g2
        simp
        replace g2 : (7 : ℝ) ≤ (11 / 4) ^ 2:= by linarith
        replace g2:= Real.sqrt_le_sqrt g2
        field_simp at g2
        linarith
      rw [g2] at g1
      simp at g1
      -- Continue applying the recurrence relation
      replace g2:= (h2 (n + 1) (by omega)).2 (by rw [g1] ; decide)
      rw [g1] at g2
      simp at g2
      rw [show n + 1 + 1 = n + 2 by omega] at g2
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num] at g2
      field_simp at g2
      simp at g2
      have g3:= (h2 (n + 2) (by omega)).1 (by rw [g2] ; decide)
      rw [g2] at g3
      simp at g3
      rw [show n + 2 + 1 = n + 3 by omega] at g3
      have g4:= (h2 (n + 3) (by omega)).1 (by rw [g3] ; decide)
      rw [g3] at g4
      simp at g4
      rw [show n + 3 + 1 = n + 4 by omega] at g4
      exact g4
    -- Case analysis on M = 2 or M = 3
    rcases hMpos with ⟨rfl, rfl⟩
    .
      -- Case: M = 2
      simp at hM hm2
      -- Apply the recurrence relation for odd numbers
      have g1:= (h2 n (by omega)).2 (by rw [←hM] ; decide)
      rw [←hM] at g1
      norm_num at g1
      -- Show that ⌊√5⌋ = 2
      have g2 : ⌊√5⌋ = 2:= by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        simp
        have g2 : (5 : ℝ) ≥ 2 ^ 2:= by linarith
        replace g2:= Real.sqrt_le_sqrt g2
        field_simp at g2
        exact g2
        simp
        replace g2 : (5 : ℝ) ≤ (5 / 2) ^ 2:= by linarith
        replace g2:= Real.sqrt_le_sqrt g2
        field_simp at g2
        linarith
      rw [g2] at g1
      simp at g1
      -- Use the previous result to show a_{n+5} = 3
      replace g2:= g (n + 1) (by omega) g1
      rw [show n + 1 + 4 = n + 5 by omega] at g2
      -- Show that this violates the minimality of M
      simp [lowerBounds] at hm2
      replace hm2:= hm2 (n + 5) (by omega) (show a (n + 5) = a (n + 5) by simp)
      linarith
    .
      -- Case: M = 3
      subst M
      simp at hM
      -- Use the previous result to show a_{n+4} = 3
      have g1:= g n (by omega) (by rw [hM])
      -- Show that this violates the minimality of M
      simp [lowerBounds] at hm2
      replace hm2:= hm2 (n + 4) (by omega) (show a (n + 4) = a (n + 4) by simp)
      linarith
