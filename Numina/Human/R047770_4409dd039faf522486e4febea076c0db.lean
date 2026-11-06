import Mathlib

/- 2. (a) $[\mathbf{6}]$ Let $P$ be a graph with one vertex $v_{n}$ for each positive integer $n$. If $a < b$, then an edge connects vertices $v_{a}$ and $v_{b}$ if and only if $\frac{b}{a}$ is a prime number. What is the chromatic number of $P$ ? Prove your answer. -/
theorem number_theory_156032 (G : SimpleGraph ℕ+)
  (hG : ∀ a b, a < b → (G.Adj a b ↔ ∃ p, Nat.Prime p ∧ a ∣ b ∧ p = b / a))
  : G.chromaticNumber = 2 := by

    -- The chromatic number is at least 2, because it has some edge
    have at_least_two : 2 ≤ G.chromaticNumber := by
      -- 2 and 4 are adjacent
      have adj := (hG 2 4 (by decide)).mpr ⟨2, by decide, PNat.dvd_iff'.mpr rfl, by decide⟩
      exact SimpleGraph.two_le_chromaticNumber_of_adj adj

    -- The chromatic number is less than 2
    have colorable_two : G.chromaticNumber ≤ 2 := by
      convert_to G.chromaticNumber ≤ (2 : ℕ)
      -- because we have a valid coloring with two colors
      rw [SimpleGraph.chromaticNumber_le_iff_colorable]
      refine ⟨?_, ?_⟩
      -- We color each number by the parity of its number of primefactors
      · intro n
        exact ⟨n.val.primeFactorsList.length % 2, Nat.mod_lt _ <| by decide⟩

      -- Let aa and bb be adjacent
      · intro aa bb adj
        simp only [SimpleGraph.top_adj, ne_eq, Fin.mk.injEq]
        -- wlog aa < bb
        wlog hue : aa < bb generalizing aa bb
        · cases' eq_or_lt_of_le (not_lt.mp hue) with eq lt
          · simp only [eq, SimpleGraph.irrefl] at adj
          · exact fun a => this adj.symm lt a.symm

        -- Then bb = aa * p for some prime
        obtain ⟨p, hp, p1, p2⟩ := (hG _ _ hue).mp adj
        have bb_eq : (bb : ℕ) = (aa : ℕ) * p := by
          refine (Nat.div_eq_iff_eq_mul_right ?_ ?_).mp ?_
          exact PNat.pos aa
          exact PNat.dvd_iff.mp p1
          exact p2.symm

        -- then bb has one more prime factor than aa
        apply_fun (fun x => x.primeFactorsList.length) at bb_eq
        have aa_ne_zero : (aa : ℕ) ≠ 0 := PNat.ne_zero aa
        have p_ne_zero : p ≠ 0 := by
          rw [p2]
          simp only [ne_eq, Nat.div_eq_zero_iff, PNat.ne_zero, PNat.coe_lt_coe, false_or, not_lt]
          exact le_of_lt hue

        have factors_perm := Nat.perm_primeFactorsList_mul aa_ne_zero p_ne_zero
        rw [Nat.primeFactorsList_prime hp] at factors_perm
        simp only [bb_eq, factors_perm.length_eq, List.length_append, List.length_singleton, ne_eq]

        -- so their parity is different
        rw [Nat.add_mod]
        have := @Nat.mod_lt ((aa : ℕ).primeFactorsList.length) 2 <| by decide
        interval_cases (aa : ℕ).primeFactorsList.length % 2 <;> decide

    -- le antisymm for ℕ∞, so the chromatic number is two
    cases' h : G.chromaticNumber with aa bb
    · simp only [h, top_le_iff] at colorable_two
      exact colorable_two.symm
    · simp only [h, Nat.ofNat_le_cast, Nat.cast_le_ofNat] at at_least_two colorable_two
      norm_cast
      exact (Nat.le_antisymm at_least_two colorable_two).symm