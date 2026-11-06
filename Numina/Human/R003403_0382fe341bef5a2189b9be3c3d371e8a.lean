import Mathlib
/- 2.48 Find all sets of distinct positive integers (at least 2) such that the sum of the numbers equals their product. -/
theorem number_theory_176912 : {A : Finset ℕ | A.card ≥ 2 ∧ A.sum (fun x => x) = A.prod (fun x => x)} = {{1, 2, 3}}:= by
  ext A
  constructor
  .
    -- Forward direction: if A satisfies the conditions, then A = {1, 2, 3}
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- First, prove that all elements in A are positive
    have h3 : ∀ x ∈ A, x > 0:= by
      by_contra H
      simp at H
      have h3 : ∏ x ∈ A, x = 0:= by exact Finset.prod_eq_zero H rfl
      rw [h3] at h2
      simp at h2
      replace h2 : A = {0}:= by
        ext x
        constructor
        intro h
        simp
        exact h2 x h
        intro h
        simp at h
        subst x
        exact H
      replace h2 : A.card = 1:= by rw [h2] ; simp
      omega
    -- Consider cases based on the cardinality of A
    replace h1 : A.card = 2 ∨ A.card = 3 ∨ A.card ≥ 4:= by omega
    rcases h1 with h1 | h1 | h1
    .
      -- Case 1: A has exactly 2 elements
      replace h1 : (↑A : Set ℕ).ncard = 2:= by
        simp
        exact h1
      apply Set.ncard_eq_two.1 at h1
      rcases h1 with ⟨x, y, hxy, h1⟩
      simp at h1
      subst A
      simp [hxy] at h2
      have g1:= h3 x (by simp)
      have g2:= h3 y (by simp)
      -- Set a = x-1, b = y-1 to work with non-negative integers
      set a:= x - 1 with ha
      set b:= y - 1 with hb
      clear_value a b
      replace ha : x = a + 1:= by omega
      replace hb : y = b + 1:= by omega
      subst x y
      replace h2 : a * b = 1:= by linarith
      simp at h2
      rcases h2 with ⟨rfl, rfl⟩
      simp at hxy
    .
      -- Case 2: A has exactly 3 elements
      replace h1 : (↑A : Set ℕ).ncard = 3:= by
        simp
        exact h1
      apply Set.ncard_eq_three.1 at h1
      rcases h1 with ⟨x, y, z, hxy, hxz, hyz, h1⟩
      replace h1 : A = ({x, y, z} : Finset ℕ):= by
        suffices (↑A : Set ℕ) = ({x, y, z} : Finset ℕ) by exact Finset.coe_inj.mp this
        rw [h1]
        simp
      subst A
      simp [hxy, hxz, hyz] at h2
      have g1:= h3 x (by simp)
      have g2:= h3 y (by simp)
      have g3:= h3 z (by simp)
      -- Set a = x-1, b = y-1, c = z-1 to work with non-negative integers
      set a:= x - 1 with ha
      set b:= y - 1 with hb
      set c:= z - 1 with hc
      clear_value a b c
      replace ha : x = a + 1:= by omega
      replace hb : y = b + 1:= by omega
      replace hc : z = c + 1:= by omega
      subst x y z
      clear h3
      replace h2 : a * b * c + a * b + b * c + a * c = 2:= by linarith
      clear g1 g2 g3
      -- Consider whether all a, b, c are non-zero
      by_cases g : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0
      .
        -- If all are non-zero, the product dominates the sum
        rcases g with ⟨ha, hb, hc⟩
        have g1 : a * b * c ≠ 0:= by positivity
        have g2 : a * b ≠ 0:= by positivity
        have g3 : b * c ≠ 0:= by positivity
        omega
      .
        -- If at least one is zero, analyze the remaining equation
        replace g : a = 0 ∨ b = 0 ∨ c = 0:= by omega
        -- Helper lemma: if x * y = 2, then (x,y) = (2,1) or (1,2)
        have g1 : ∀ x y : ℕ, x * y = 2 → (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2):= by
          intro x y hxy
          have g1 : x > 0:= by
            by_contra H
            simp at H
            subst x
            simp at hxy
          have g2 : y > 0:= by
            by_contra H
            simp at H
            subst y
            simp at hxy
          set x1:= x - 1 with hx1
          set y1:= y - 1 with hy1
          clear_value x1 y1
          replace hx1 : x = x1 + 1:= by omega
          replace hy1 : y = y1 + 1:= by omega
          subst x y
          by_cases g3 : x1 = 0 ∨ y1 = 0
          .
            rcases g3 with g3 | g3
            .
              subst x1
              simp at hxy
              subst y1
              simp
            .
              subst y1
              simp at hxy
              subst x1
              simp
          .
            simp at g3
            rcases g3 with ⟨g3, g4⟩
            replace g3 : x1 + 1 ≥ 2:= by omega
            replace g4 : y1 + 1 ≥ 2:= by omega
            replace g3 : (x1 + 1) * (y1 + 1) ≥ 2 * 2:= by exact Nat.mul_le_mul g3 g4
            linarith
        -- Apply the helper lemma to each case where one variable is zero
        rcases g with g | g | g
        all_goals
          subst g
          simp at h2
          replace g1:= g1 _ _ h2
          rcases g1 with g1 | g1
          all_goals
            rcases g1 with ⟨rfl, rfl⟩
            simp
          all_goals
            ext x
            simp
            omega
    .
      -- Case 3: A has 4 or more elements
      -- Prove that for sets with 4+ elements where all elements ≥ 2, sum < product
      have h : ∀ n : ℕ, ∀ A : Finset ℕ, A.card = n + 3 → (∀ x ∈ A, x ≥ 2) → 1 + ∑ x ∈ A, x < ∏ x ∈ A, x:= by
        intro n
        induction n with
        | zero =>
          -- Base case: 3 elements all ≥ 2
          intro A hA h
          simp at hA
          replace hA : (↑A : Set ℕ).ncard = 3:= by
            simp
            exact hA
          apply Set.ncard_eq_three.1 at hA
          rcases hA with ⟨x, y, z, hxy, hxz, hyz, hA⟩
          replace h1 : A = ({x, y, z} : Finset ℕ):= by
            suffices (↑A : Set ℕ) = ({x, y, z} : Finset ℕ) by exact Finset.coe_inj.mp this
            rw [hA]
            simp
          subst h1
          simp [hxy, hxz, hyz]
          have g1:= h x (by simp)
          have g2:= h y (by simp)
          have g3:= h z (by simp)
          -- Set a = x-2, b = y-2, c = z-2 to work with non-negative integers
          set a:= x - 2 with ha
          set b:= y - 2 with hb
          set c:= z - 2 with hc
          clear_value a b c
          replace ha : x = a + 2:= by omega
          replace hb : y = b + 2:= by omega
          replace hc : z = c + 2:= by omega
          subst x y z
          ring_nf
          omega
        | succ n ih =>
          -- Inductive step: for n+4 elements
          intro A hA h
          have g : A.Nonempty:= by
            replace hA : A.card ≠ 0:= by omega
            exact Finset.card_ne_zero.mp hA
          replace g:= Finset.Nonempty.exists_cons_eq g
          rcases g with ⟨A1, t, hA1, hA2⟩
          rw [←hA2]
          simp [hA1]
          have gt:= h t (by rw [←hA2] ; simp)
          replace h : ∀ x ∈ A1, x ≥ 2:= by
            intro x hx
            rw [←hA2] at h
            exact h x (by simp ; right ; exact hx)
          -- Product of A1 is at least 2^|A1|
          have g2 : ∏ x ∈ A1, x ≥ 2 ^ A1.card:= by exact Finset.pow_card_le_prod A1 (fun x => x) 2 h
          rw [←hA2] at hA
          simp [hA1] at hA
          have g3 : A1.card ≥ 1:= by omega
          replace g2 : ∏ x ∈ A1, x ≥ 2 ^ 1:= by
            have g2 : 2 ^ A1.card ≥ 2 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) g3
            linarith
          simp at g2
          replace ih:= ih A1 hA h
          set t1:= t - 1 with ht1
          clear_value t1
          replace ht1 : t = t1 + 1:= by omega
          subst t
          replace g2 : 2 * t1 ≤ (∏ x ∈ A1, x) * t1:= by exact Nat.mul_le_mul_right t1 g2
          linarith
      -- Apply the lemma to show that if all elements ≥ 2, then sum < product
      by_cases h4 : ∀ x ∈ A, x ≥ 2
      .
        specialize h (A.card - 3) A (by omega) h4
        linarith
      .
        -- If not all elements ≥ 2, then one element must be 1
        simp at h4
        rcases h4 with ⟨x, hx, hx1⟩
        have hx2:= h3 x hx
        replace hx1 : x = 1:= by omega
        subst x
        clear hx2
        -- Remove 1 from A to get A1
        set A1:= A \ {1} with hA1
        clear_value A1
        have h5 : 1 ∉ A1:= by
          subst A1
          by_contra H
          simp at H
        have h4 : A = Finset.cons 1 A1 h5:= by
          subst A1
          ext x
          constructor
          .
            intro g
            simp
            by_cases g1 : x = 1
            .
              left
              exact g1
            .
              right
              exact ⟨g, g1⟩
          .
            intro g
            simp at g
            rcases g with g | g
            .
              subst x
              exact hx
            .
              exact g.1
        rw [h4] at h2 h1
        simp [h5] at h2 h1
        -- All elements in A1 must be ≥ 2
        replace h3 : ∀ x ∈ A1, x ≥ 2:= by
          by_contra H
          simp at H
          rcases H with ⟨x, gx, gx1⟩
          rw [h4] at h3
          have gx2 : x ≠ 1:= by
            by_contra H1
            subst x A1
            simp at gx
          replace h3:= h3 x (by simp [gx2] ; exact gx)
          omega
        -- Apply the lemma to A1
        replace h:= h (A1.card - 3) A1 (by omega) h3
        omega
  .
    -- Backward direction: if A = {1, 2, 3}, then A satisfies the conditions
    intro h
    simp at h
    subst A
    simp
