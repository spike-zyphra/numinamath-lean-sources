import Mathlib

/- Let $f$ be a function from $R \rightarrow R$, and
(1) for any $x, y \in R$,
$$
f(x)+f(y)+1 \geqslant f(x+y) \geqslant f(x)+f(y) ;
$$
(2) for any $x \in [0,1)$, $f(0) \geqslant f(x)$;
$$
\text{(3) } -f(-1)=f(1)=1 \text{.}
$$

Find all functions that satisfy the conditions. -/

theorem algebra_304444 (f : ℝ → ℝ)
    (h1 : ∀ x y, f x + f y + 1 ≥ f (x + y) ∧ f (x + y) ≥ f x + f y)
    (h2 : ∀ x ∈ Set.Ico 0 1, f 0 ≥ f x)
    (h3 : -f (-1) = 1 ∧ f 1 = 1) :
    ∀ x, f x = ⌊x⌋ := by

    -- we first show that f 0 = 0
    have h0: f 0 = 0 := by
        have g1:= h1 0 0
        norm_num at g1
        rcases g1 with ⟨g1,g2⟩
        have g3:= h1 (1/2) (1/2)
        norm_num at g3
        rcases g3 with ⟨g3,g4⟩
        have g5:= h1 1 0
        norm_num at g5
        rcases g5 with ⟨g5,g6⟩
        simp [h3] at *
        specialize h2 (1 / 2)
        norm_num at h2
        clear * - g2 g3 h2
        nlinarith

    -- then we show that f x = 0 for all x in [0,1)
    have l: ∀ x ∈ Set.Ico 0 1, f x = 0 := by
        intro x hx
        simp at hx
        by_cases i: x = 0
        .   -- case 1: x = 0
            simp [i,h0]
        .   -- case 2: x ∈ (0,1)
            rcases hx with ⟨l1, l2⟩
            replace l1: 0 < x := by
                by_contra! o
                replace o: x = 0 := by
                    linarith
                simp [o] at i
            clear i
            have g1:= h2 x
            have r: 0 ≤ x := by linarith
            simp [l1,l2,r] at g1
            have g2:= h2 (1 - x)
            have s: x ≤ 1 := by linarith
            simp [l1,l2,s] at g2
            clear s h2 r
            simp [h0] at g1 g2
            specialize h1 x (1 - x)
            rcases h1 with ⟨s1,s2⟩
            clear s2
            norm_num at s1
            rcases h3 with ⟨s3,s4⟩
            simp [s4] at s1
            nlinarith

    -- Next step, we show that f(x + 1) =  f x + 1
    have g: ∀ x, f (x + 1) = f x + 1 := by
        intro x
        have h':= h1
        specialize h1 x 1
        rcases h1 with ⟨h1,h2⟩
        clear h1
        rcases h3 with ⟨f1,f2⟩
        simp [f2] at h2
        specialize h' (x + 1) (-1)
        rcases h' with ⟨h3,h4⟩
        clear h3
        norm_num at h4
        replace f1: f (-1) = - 1 := by linarith
        simp [f1] at h4
        clear * - h2 h4
        linarith

    -- then we can use the previous results to show that f x = ⌊x⌋
    -- we induction by two cases: positive and negative

    have h_pos: ∀ n: ℕ, ∀ x: ℝ, n ≤ x ∧ x < (n + 1) → f x = n := by  -- x is positive
        intro n
        induction' n with n ih
        .   -- base case: n = 0
            intro x o
            rcases o with ⟨l1, l2⟩
            specialize l x
            simp at l l1 l2
            simp [l1,l2] at l
            simp
            exact l
        .   -- inductive case: n > 0
            intro x o
            rcases o with ⟨l1, l2⟩
            simp
            specialize g (x - 1)
            specialize ih (x - 1)
            norm_num at g
            simp [g]
            simp at l1 l2
            have r1: n ≤ x - 1 := by
                linarith
            have r2: x - 1 < n + 1 := by
                linarith
            simp [r1,r2] at ih
            clear r1 r2
            exact ih

    have h_neg: ∀ n: ℕ, ∀ x: ℝ, - (n + 1) ≤ x ∧ x < -n → f x = - (n + 1) := by -- x is negative
        intro n
        induction' n with n ih
        .   -- base case: n = 0
            intro x o
            rcases o with ⟨l1, l2⟩
            have l':= l
            specialize l x
            simp at l l1 l2
            simp [l1,l2] at l
            simp
            specialize g x
            replace g: f x = f (x + 1) - 1 := by linarith
            rw [g]
            norm_num
            clear l g
            specialize l' (x + 1)
            simp at h2
            have r1: 0 ≤ x + 1 := by
                linarith
            have r2: x < 0 := by
                linarith
            simp [r1,r2] at l'
            clear r1 r2
            exact l'
        .   -- inductive case: n > 0
            intro x o
            rcases o with ⟨l1, l2⟩
            specialize g x
            replace g: f x = f (x + 1) - 1 := by linarith
            simp [g]
            clear g
            specialize ih (x + 1)
            simp at l1 l2
            have r1: - (n + 1) ≤ x + 1 := by
                linarith
            have r2: x + 1 < -n := by
                linarith
            simp [r1,r2] at ih
            clear r1 r2
            have r: - 1 ≤ x + 1 + n := by
                linarith
            simp [r] at ih
            clear r
            simp [ih]
            ring

    -- At last, we can splits two cases to show that f x = ⌊x⌋
    intro x
    by_cases lx: 0 ≤ x

    .   -- case 1: x is positive
        clear h_neg
        set n:= ⌊x⌋ with hn
        have s: 0 ≤ n := by
            rw [hn]
            rw [Int.floor_nonneg]
            exact lx
        have o: n.natAbs ≤ x ∧ x < n.natAbs + 1 := by
            rw [hn]
            constructor
            .
                rw [Nat.cast_natAbs]
                rw [show |⌊x⌋| = ⌊x⌋ by apply abs_of_nonneg; linarith]
                apply Int.floor_le
            .
                rw [Nat.cast_natAbs]
                rw [show |⌊x⌋| = ⌊x⌋ by apply abs_of_nonneg; linarith]
                apply Int.lt_floor_add_one

        specialize h_pos n.natAbs x o
        rw [h_pos]
        rw [Nat.cast_natAbs]
        rw [show |n| = n by apply abs_of_nonneg; linarith]

    .   -- case 2: x is negative
        clear h_pos
        simp at lx
        set n:= - ⌊x⌋ - 1 with hn
        have s: 0 ≤ n := by
            rw [hn]
            have j: ⌊x⌋ ≤ x := by apply Int.floor_le
            replace j: ⌊x⌋ < (0: ℝ) := by nlinarith
            simp at j
            omega
        have o: - (n.natAbs + 1) ≤ x ∧ x < - (n.natAbs) := by
            rw [hn]
            constructor
            .
                rw [Nat.cast_natAbs]
                have eq: |-⌊x⌋ - 1| = -⌊x⌋ - 1 := by
                    apply abs_of_nonneg
                    linarith
                rw [eq]
                have i:= Int.floor_le x
                simp
                nlinarith
            .
                rw [Nat.cast_natAbs]
                have eq: |-⌊x⌋ - 1| = -⌊x⌋ - 1 := by
                    apply abs_of_nonneg
                    linarith
                rw [eq]
                have i:= Int.lt_floor_add_one x
                simp
                linarith
        specialize h_neg n.natAbs x o
        rw [h_neg]
        rw [Nat.cast_natAbs]
        rw [show |n| = n by apply abs_of_nonneg; linarith]
        rw [hn]
        simp