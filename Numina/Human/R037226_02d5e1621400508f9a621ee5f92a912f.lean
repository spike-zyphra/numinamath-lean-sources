import Mathlib

/- (Hungary, 1982). Let $n \in \mathbb{N}^{*}$. Show that if the equation $x^{3}-3 x y^{2}+y^{3}=n$ has a solution $(x, y) \in \mathbb{Z}^{2}$, it has at least three. Show that for $n=2009$, this equation has no solution. -/

theorem number_theory_125692 (n : ℕ) (hn : n ≠ 0) :
    (∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = n) →
    (n = 2009 → ¬∃ x y : ℤ, x^3 - 3 * x * y^2 + y^3 = n) ∧
    (Infinite {p : ℤ × ℤ | p.1^3 - 3 * p.1 * p.2^2 + p.2^3 = n} -- Needed because ncard is 0 if set is infinite
    ∨ {p : ℤ × ℤ | p.1^3 - 3 * p.1 * p.2^2 + p.2^3 = n}.ncard ≥ 3) := by

  intro h
  constructor
  . intro hn
    -- Suppose that $n = 2009$.
    -- We proceed by contradiction.
    by_contra g
    rw [hn] at g
    -- Let $x,y$ satisfy the equation $x^3 - 3xy^2 + y^3 = 2009$.
    obtain ⟨ x, y, hxy ⟩ := g
    zify at hxy
    -- It is easy to see that $k \equiv k^3 \pmod 3$ for all integers $k.$
    have claim1 (k : ℤ) : k ≡ k ^ 3 [ZMOD 3] := by
      mod_cases k % 3
      . have : k ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by exact Int.ModEq.pow 3 H
        rw [zero_pow] at this
        . exact Int.ModEq.trans H (id (Int.ModEq.symm this))
        . norm_num
      . have : k ^ 3 ≡ 1 ^ 3 [ZMOD 3] := by exact Int.ModEq.pow 3 H
        rw [one_pow] at this
        exact Int.ModEq.trans H (id (Int.ModEq.symm this))
      . have : k ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by exact Int.ModEq.pow 3 H
        simp at this
        exact Int.ModEq.trans H (id (Int.ModEq.symm this))

    -- Note that $x + y = 2009 + 3xy^2 \equiv 2 \pmod 3$.
    have claim2 : x + y ≡ 2 [ZMOD 3] := by
      have hx : x ≡ x ^ 3 [ZMOD 3] := by apply claim1
      have hy : y ≡ y ^ 3 [ZMOD 3] := by apply claim1
      calc
        _ ≡ x ^ 3 + y ^ 3 [ZMOD 3] := by exact Int.ModEq.add (claim1 x) (claim1 y)
        _ = 2009 + 3 * (x * y ^ 2) := by rw [← hxy]; ring
        _ ≡ 2 [ZMOD 3] := by exact Int.modEq_add_fac_self

    -- It follows that $x^3 - 3xy^2 + y^3 \equiv -1 \pmod 9$.
    have claim3 : x ^ 3 - 3 * x * y ^ 2 + y ^ 3 ≡ -1 [ZMOD 9] := by
      have m0 (k : ℤ) (hk : k ≡ 0 [ZMOD 3]) : k ^ 3 ≡ 0 [ZMOD 9] := by
        have : ∃ r : ℤ, k = 3 * r := by refine exists_eq_mul_right_of_dvd ?_; exact Int.dvd_of_emod_eq_zero hk
        obtain ⟨ r, hr ⟩ := this
        rw [hr]
        calc
          _ = 9 * (3 * r ^ 3) := by ring
          _ ≡ 0 [ZMOD 9] := by refine Dvd.dvd.modEq_zero_int ?_
                               apply Int.dvd_mul_right
      have m1 (k : ℤ) (hk : k ≡ 1 [ZMOD 3]) : k ^ 3 ≡ 1 [ZMOD 9] := by
        have : ∃ r : ℤ, k = 3 * r + 1 := by
          apply Int.dvd_sub_of_emod_eq at hk
          obtain ⟨ s, hs ⟩ := hk
          use s
          rw [← hs]
          simp
        obtain ⟨ r, hr ⟩ := this
        rw [hr]
        calc
          _ = 9 * (3 * r ^3 + 3 * r ^ 2 + r) + 1 := by ring
          _ ≡ 0 + 1 [ZMOD 9] := by refine Int.ModEq.add ?_ ?_
                                   . refine Dvd.dvd.modEq_zero_int ?_
                                     apply Int.dvd_mul_right
                                   . decide
          _ ≡ _ [ZMOD 9] := by decide
      have m2 (k : ℤ) (hk : k ≡ 2 [ZMOD 3]) : k ^ 3 ≡ -1 [ZMOD 9] := by
        have : ∃ r : ℤ, k = 3 * r + 2 := by
          apply Int.dvd_sub_of_emod_eq at hk
          obtain ⟨ s, hs ⟩ := hk
          use s
          rw [← hs]
          simp
        obtain ⟨ r, hr ⟩ := this
        rw [hr]
        calc
          _ = 9 * (3 * r ^3 + 6 * r ^ 2 + 4 * r) + 8 := by ring
          _ ≡ 0 + 8 [ZMOD 9] := by refine Int.ModEq.add ?_ ?_
                                   . refine Dvd.dvd.modEq_zero_int ?_
                                     apply Int.dvd_mul_right
                                   . decide
          _ ≡ _ [ZMOD 9] := by decide

      mod_cases x % 3
      . have hy : y ≡ 2 [ZMOD 3] := by exact Int.ModEq.add_left_cancel H claim2
        calc
          _ = x ^ 3 + y ^ 3 - 3 * x * y ^ 2 := by ring
          _ ≡ 0 + (-1) - 3 * x * y ^ 2 [ZMOD 9] := by
                refine Int.ModEq.sub ?_ rfl
                exact Int.ModEq.add (m0 x H) (m2 y hy)
          _ = -1 - 3 * x * y ^ 2 := by simp
          _ ≡ -1 - 0 [ZMOD 9] := by
                have : 3 * x * y ^ 2 ≡ 0 [ZMOD 9] := by
                  have : ∃ r : ℤ, x = 3 * r := by refine exists_eq_mul_right_of_dvd ?_
                                                  exact Int.dvd_of_emod_eq_zero H
                  obtain ⟨ r, hr ⟩ := this
                  rw [hr]
                  rw [← mul_assoc]
                  simp
                  rw [mul_assoc]
                  refine Dvd.dvd.modEq_zero_int ?_
                  apply Int.dvd_mul_right
                exact Int.ModEq.symm (Int.ModEq.sub_left (-1) (id (Int.ModEq.symm this)))
          _ ≡ _ [ZMOD 9] := by simp
      . have hy : y ≡ 1 [ZMOD 3] := by exact Int.ModEq.add_left_cancel H claim2
        calc
          _ = x ^ 3 + y ^ 3 - 3 * x * y ^ 2 := by ring
          _ ≡ 1 + 1 - 3 * x * y ^ 2 [ZMOD 9] := by
                refine Int.ModEq.sub ?_ rfl
                exact Int.ModEq.add (m1 x H) (m1 y hy)
          _ = 2 - 3 * x * y ^ 2 := by simp
          _ ≡ 2 - 3 [ZMOD 9] := by
                have : 3 * x * y ^ 2 ≡ 3 [ZMOD 9] := by
                  have : ∃ r : ℤ, x = 3 * r + 1 := by
                    apply Int.dvd_sub_of_emod_eq at H
                    obtain ⟨ s, hs ⟩ := H
                    use s
                    rw [← hs]
                    simp
                  obtain ⟨ r, hr ⟩ := this
                  rw [hr]
                  have : ∃ s : ℤ, y = 3 * s + 1 := by
                    apply Int.dvd_sub_of_emod_eq at hy
                    obtain ⟨ s, hs ⟩ := hy
                    use s
                    rw [← hs]
                    simp
                  obtain ⟨ s, hs ⟩ := this
                  rw [hs]
                  calc
                    _ = 9 * (9*r*s^2 + 6*r*s + r + 3*s^2 + 2*s) + 3 := by ring
                    _ ≡ _ [ZMOD 9] := by
                          have : 9 * (9*r*s^2 + 6*r*s + r + 3*s^2 + 2*s) ≡ 0 [ZMOD 9] := by
                            refine Dvd.dvd.modEq_zero_int ?_
                            apply Int.dvd_mul_right
                          calc
                            _ ≡ 0 + 3 [ZMOD 9] := by exact Int.ModEq.add this rfl
                            _ = 3 := by rw [zero_add]
                exact Int.ModEq.symm (Int.ModEq.sub_left 2 (id (Int.ModEq.symm this)))
          _ ≡ _ [ZMOD 9] := by simp
      . have hy : y ≡ 0 [ZMOD 3] := by exact Int.ModEq.add_left_cancel H claim2
        calc
          _ = x ^ 3 + y ^ 3 - 3 * x * y ^ 2 := by ring
          _ ≡ -1 + 0 - 3 * x * y ^ 2 [ZMOD 9] := by
                refine Int.ModEq.sub ?_ rfl
                exact Int.ModEq.add (m2 x H) (m0 y hy)
          _ = -1 - 3 * x * y ^ 2 := by simp
          _ ≡ -1 - 0 [ZMOD 9] := by
                have : 3 * x * y ^ 2 ≡ 0 [ZMOD 9] := by
                  have : ∃ r : ℤ, y = 3 * r := by refine exists_eq_mul_right_of_dvd ?_
                                                  exact Int.dvd_of_emod_eq_zero hy
                  obtain ⟨ r, hr ⟩ := this
                  rw [hr]
                  calc
                    _ = 9 * (3 * x * r ^ 2) := by ring
                    _ ≡ _ [ZMOD 9] := by refine Dvd.dvd.modEq_zero_int ?_
                                         apply Int.dvd_mul_right
                exact Int.ModEq.symm (Int.ModEq.sub_left (-1) (id (Int.ModEq.symm this)))
          _ ≡ _ [ZMOD 9] := by simp

    -- But $2009 \equiv 2 \pmod 9$.
    have claim4 : 2009 ≡ 2 [ZMOD 9] := by decide

    -- Thus $-1 \equiv 2 \pmod 9$, which is impossible.
    rw [hxy] at claim3
    have : -1 ≡ 2 [ZMOD 9] := by exact id (Int.ModEq.symm claim3)
    revert this
    decide

  . -- Suppose that $x, y$ satisfy $x^3 - 3xy^2 + y^3 = n$.
    obtain ⟨ x, y, hxy ⟩ := h
    -- Let $p = (x,y)$.
    set p := (x, y)
    -- Let $q = (-y,x-y)$.
    set q := (-y, x - y)
    -- Let $r = (y-x,-x)$.
    set r := (y - x, -x)

    -- Let $t$ denote the set $\{ p ∈ ℤ^2 | p_1^3 - 3p_1p_2^2 + p_2^3 = n\}$.
    set t := {p : ℤ × ℤ | p.1^3 - 3 * p.1 * p.2^2 + p.2^3 = n}

    -- Let $s$ denote the set $\{p, q, r\}$
    set s : Finset (ℤ × ℤ) := {p, q, r}

    -- We see that $p ≠ q$ and $q ≠ r$ and $p ≠ r$ and so $|s| = 3$.
    have scard : s.card = 3 := by
      simp [s]
      refine Finset.card_eq_succ.mpr ?_
      use p, {q, r}
      constructor
      . simp
        by_contra g
        rw [Classical.not_and_iff_or_not_not] at g
        repeat rw [ Classical.not_not] at g
        obtain g' | g' := g
        . simp [p, q] at g'
          have hy : y = 0 := by omega
          have hx : x = 0 := by omega
          simp [hy, hx] at hxy
          norm_cast at hxy
          omega
        . simp [p, r] at g'
          have hy : y = 0 := by omega
          have hx : x = 0 := by omega
          simp [hy, hx] at hxy
          norm_cast at hxy
          omega
      . apply And.intro rfl
        refine Finset.card_eq_succ.mpr ?_
        use q, {r}
        constructor
        . simp
          by_contra g
          simp [q, r] at g
          have hy : y = 0 := by omega
          have hx : x = 0 := by omega
          simp [hy, hx] at hxy
          norm_cast at hxy
          omega
        . apply And.intro rfl
          simp

    -- Note that $s$ is a subset of $t$.
    have ssubsetoft : s.toSet ⊆ t := by
      refine Set.subset_setOf.mpr ?_
      intro x
      simp [s]
      intro pqr
      obtain g | g | g := pqr
      . rw [g]
        simp [p]
        exact hxy
      . rw [g]
        simp [q]
        rw [← hxy]
        ring_nf
      . rw [g]
        simp [r]
        rw [← hxy]
        ring_nf

    -- We now proceed by contradiction
    by_contra g
    -- Then $t$ is finite with cardinality less than 3.
    push_neg at g
    obtain ⟨ gl, gr ⟩ := g

    -- But this is impossible since $s$ is a subset of $t$ and has
    -- cardinality 3.
    have : s.toSet.ncard = 3 := by
      rw [← scard]
      exact Set.ncard_coe_Finset s
    rw [← this] at gr
    simp at gl
    revert gr
    have : (s.toSet).ncard ≤ t.ncard := by exact Set.ncard_le_ncard ssubsetoft gl
    omega