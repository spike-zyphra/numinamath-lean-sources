import Mathlib

/- Given that the domain of the function $f(x)$ is $R$, it satisfies:
(1) $f(x)$ is an even function;
(2) for any $x \in R$, $f(x+4) = f(x)$, and when $x \in [0,2]$, $f(x) = x + 2$.
Then the distance between the two closest intersection points of the line $y=4$ and the graph of the function $f(x)$ is -/

theorem algebra_634193 {f : ℝ → ℝ}
    (h0 : ∀ x, f (-x) = f x)
    (h1 : ∀ x, f (x + 4) = f x)
    (h2 : ∀ x ∈ Set.Icc 0 2, f x = x + 2) :
    IsLeast {d | ∃ x1 x2, x1 < x2 ∧ d = x2 - x1 ∧ f x1 = 4 ∧ f x2 = 4} 4 := by

    -- we show that f x = 4 iff x = 4k + 2
    have h: ∀ x, f x = 4 ↔ ∃ k: ℤ, x = 4 * k + 2 := by

      -- note that we only need to prove for the case for 0 ≤ x since f is even
      suffices h: ∀ x, 0 ≤ x → (f x = 4 ↔ ∃ k: ℤ, x = 4 * k + 2) by
        intro x
        by_cases r: 0 ≤ x
        .
          exact h x r

        -- case x < 0, use symmetry
        .
          simp at r
          specialize h (-x) (by linarith)
          specialize h0 x
          rw [h0] at h
          rw [h]
          clear *-
          constructor
          .
            intro h
            obtain ⟨s, h⟩ := h
            use - (s + 1)
            simp
            linarith
          .
            intro h
            obtain ⟨s, h⟩ := h
            use - (s + 1)
            simp
            linarith

      -- using induction to show the case for x ∈ [4n, 4n+4]
      have h_pos: ∀ n: ℕ, ∀ x: ℝ, 4 * n ≤ x ∧ x < (4 * n + 4) → (f x = 4 ↔ ∃ k: ℤ, x = 4 * k + 2) := by
        intro n
        induction' n with n ih

        -- base case
        .
          intro x h
          simp at h
          rcases h with ⟨l1, l2⟩
          by_cases l: x ≤ 2

          -- case x ∈ [0, 2]
          .
            have v: x ∈ Set.Icc 0 2 := by
              simp
              constructor
              .
                linarith
              .
                tauto
            specialize h2 x v
            clear v
            rw [h2]
            clear h2
            constructor
            .
              intro h
              use 0
              simp
              linarith
            .
              intro h
              obtain ⟨k, h⟩ := h
              have lk: k < 1 := by
                rify
                linarith
              have rk: -1 < k := by
                rify
                linarith
              have o: k = 0 := by omega
              simp [o] at h
              rw [h]
              norm_num

          -- case x ∈ [2, 4]
          .
            simp at l
            specialize h0 x
            specialize h1 (-x)
            rw [← h0, ← h1]
            set y:= -x + 4
            have sy: y ∈ Set.Icc 0 2 := by
              simp
              refine ⟨(by simp [y]; linarith), (by simp [y]; linarith)⟩
            specialize h2 y sy
            rw [h2]
            rw [show x = 4 - y by simp [y]]
            clear *- sy
            clear_value y
            constructor
            .
              intro h
              replace h: y = 2 := by linarith
              simp [h]
              use 0
              simp
              norm_num
            .
              intro h
              obtain ⟨k, h⟩ := h
              simp at sy
              have lk: k < 1 := by
                rify
                linarith
              have rk: -1 < k := by
                rify
                linarith
              have o: k = 0 := by omega
              simp [o] at h
              linarith

        -- inductive case
        .
          intro x h
          specialize h1 (x - 4)
          rw [show x - 4 + 4 = x by ring] at h1
          rw [h1]
          specialize ih (x - 4)
          have u: 4 * ↑n ≤ x - 4 ∧ x - 4 < 4 * ↑n + 4 := by
            clear *- h
            simp at h
            constructor
            .
              nlinarith
            .
              nlinarith
          apply ih at u
          clear ih
          rw [u]
          clear *-
          constructor
          .
            intro h
            obtain ⟨s, h⟩ := h
            use (s + 1)
            simp
            linarith
          .
            intro h
            obtain ⟨s, h⟩ := h
            use (s - 1)
            simp
            linarith

      -- then we can use h_pos
      intro x h
      set q:= x / 4
      replace h: 0 ≤ q := by
        simp [q]
        linarith
      set n:= ⌊q⌋.natAbs
      specialize h_pos n x
      have u: 4 * ↑n ≤ x ∧ x < 4 * ↑n + 4 := by
        clear *- h
        refine ⟨?_, ?_⟩
        .
          suffices n ≤ q by
            simp [q] at this
            linarith
          clear_value q
          simp [n]
          rw [Nat.cast_natAbs]
          have i: 0 ≤ ⌊q⌋ := by
            rw [Int.floor_nonneg]
            tauto
          rw [show |⌊q⌋| = ⌊q⌋ by apply abs_of_nonneg; tauto]
          apply Int.floor_le
        .
          suffices q < n + 1 by
            simp [q] at this
            linarith
          clear_value q
          simp [n]
          rw [Nat.cast_natAbs]
          have i: 0 ≤ ⌊q⌋ := by
            rw [Int.floor_nonneg]
            tauto
          rw [show |⌊q⌋| = ⌊q⌋ by apply abs_of_nonneg; tauto]
          suffices q - 1 < ↑⌊q⌋ by linarith
          apply Int.sub_one_lt_floor

      apply h_pos at u
      tauto


    -- at last, we can use h to prove the original problem
    constructor

    -- the forward direction
    .
      simp
      use -2, 2
      norm_num
      have u:= h (-2)
      have v:= h 2
      constructor
      .
        rw [u]
        use -1
        simp
        norm_num
      .
        rw [v]
        use 0
        simp

    -- the backward direction
    .
      intro d hd
      simp at hd
      obtain ⟨x1, x2, l, hd, f1, f2⟩ := hd
      have u:= h x1
      have v:= h x2
      simp [f1] at u
      simp [f2] at v
      obtain ⟨k1, g1⟩ := u
      obtain ⟨k2, g2⟩ := v
      simp [g1, g2] at hd l
      rw [hd]
      norm_cast
      omega