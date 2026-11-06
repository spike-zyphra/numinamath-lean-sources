import Mathlib

/- 42nd Eötvös 1938 Problem 1 Show that a positive integer n is the sum of two squares iff 2n is the sum of two squares. -/
theorem number_theory_149607 (n : ℕ) (hn : n > 0) :
    (∃ a b : ℤ , n = a^2 + b^2) ↔ (∃ c d : ℤ, 2 * n = c^2 + d^2) := by
        constructor

        --First prove (∃ a b : ℤ , n = a^2 + b^2) → (∃ c d : ℤ, 2 * n = c^2 + d^2)
        intro h1
        --Obtain hab :  ↑n = a ^ 2 + b ^ 2.
        rcases h1 with ⟨a, b, hab⟩
        --Show 2 * n = 2 * a^2 + 2 * b^2.
        have h2n : 2 * n = 2 * a^2 + 2 * b^2 := by linarith
        --Show 2 * a^2 + 2 * b^2 = (a + b)^2 + (a - b)^2.
        have h2 : 2 * a^2 + 2 * b^2 = (a + b)^2 + (a - b)^2 := by ring
        -- Clearly (a + b), (a - b) are witnesses.
        use (a + b), (a - b)
        linarith

        --Next, prove (∃ c d : ℤ, 2 * n = c^2 + d^2) → (∃ a b : ℤ , n = a^2 + b^2).
        intro h2
        --Obtain hcd : 2 * ↑n = c ^ 2 + d ^ 2
        rcases h2 with ⟨c, d, hcd⟩
        --Show that c and d have the same parity, i.e. ¬ (Even c ∧ Odd d) ∧ ¬ (Odd c ∧ Even d).
        have h4 : ¬ (Even c ∧ Odd d) ∧ ¬ (Odd c ∧ Even d) := by
            constructor
            --Prove each component of the conjunction by way of contradiction.
            by_contra h4'
            have : Even c := by exact h4'.1
            rcases this with ⟨k₁, hk₁⟩
            have : k₁ + k₁ = 2 * k₁ := by ring
            rw [this] at hk₁
            have : Odd d := by exact h4'.2
            rcases this with ⟨k₂, hk₂⟩
            have cont1 : c^2 = 4 * k₁^2 := by
                rw [pow_two]
                repeat rw [hk₁]
                ring
            have cont2 : d^2 = 4 * k₂^2 + 4 * k₂ + 1 := by
                rw [pow_two]
                repeat rw [hk₂]
                ring_nf
            have cont3 : (c^2 + d^2) % 2 = 1 := by omega
            have cont4 : (c^2 + d^2) % 2 = 0 := by omega
            have : 0 = 1 := by omega
            --This gives a contradiction.
            contradiction

            by_contra h4'
            have : Odd c := by exact h4'.1
            rcases this with ⟨k₁, hk₁⟩
            have : Even d := by exact h4'.2
            rcases this with ⟨k₂, hk₂⟩
            have : k₂ + k₂ = 2 * k₂ := by ring
            rw [this] at hk₂
            have cont1 : c^2 = 4 * k₁^2 + 4 * k₁ + 1 := by
                rw [pow_two]
                repeat rw [hk₁]
                ring
            have cont2 : d^2 = 4 * k₂^2 := by
                rw [pow_two]
                repeat rw [hk₂]
                ring
            have cont3 : (c^2 + d^2) % 2 = 1 := by omega
            have cont4 : (c^2 + d^2) % 2 = 0 := by omega
            have : 0 = 1 := by omega
            --This gives a contradiction.
            contradiction


        --Next prove the obvious fact (Even c ∧ Odd d) ∨ (Odd c ∧ Even d) ∨ (Even c ∧ Even d) ∨ (Odd c ∧ Odd d).
        have h5 : (Even c ∧ Odd d) ∨ (Odd c ∧ Even d) ∨ (Even c ∧ Even d) ∨ (Odd c ∧ Odd d) := by
            cases' Int.even_or_odd c with hc_even hc_odd
            . simp_all only [gt_iff_lt, true_and, Int.not_odd_iff_even, not_and, Int.not_even_iff_odd, isEmpty_Prop,
              IsEmpty.forall_iff, and_true, and_self, true_or, or_true]
            . simp_all only [gt_iff_lt, not_and, Int.not_odd_iff_even, isEmpty_Prop, Int.not_even_iff_odd,
              IsEmpty.forall_iff, true_and, and_true, and_self, or_true]

        --Since  ¬ (Even c ∧ Odd d) ∧ ¬ (Odd c ∧ Even d), it follows that (Even c ∧ Even d) ∨ (Odd c ∧ Odd d).
        have h6 : (Even c ∧ Even d) ∨ (Odd c ∧ Odd d) := by tauto
        --Now do a case analysis.
        by_cases
        --Case 1: Even c ∧ Even d
        h7 : Even c ∧ Even d
        --obtain hk₁ and hk₂
        have : Even c := by exact h7.1
        rcases this with ⟨k₁, hk₁⟩
        have : k₁ + k₁ = 2 * k₁ := by linarith
        rw [this] at hk₁
        have : Even d := by exact h7.2
        rcases this with ⟨k₂, hk₂⟩
        have : k₂ + k₂ = 2 * k₂ := by linarith
        rw [this] at hk₂
        --Show that 2 * n = (2 * k₁)^2 + (2 * k₂)^2
        have h71 : 2 * n = (2 * k₁)^2 + (2 * k₂)^2 := by
            rw [hk₁, hk₂] at hcd
            exact hcd

        --Show (2 * k₁)^2 + (2 * k₂)^2 = 2 * (2 * k₁^2 + 2 * k₂^2).
        have h72 : (2 * k₁)^2 + (2 * k₂)^2 = 2 * (2 * k₁^2 + 2 * k₂^2) := by linarith

        --Show n = 2 * k₁^2 + 2 * k₂^2.
        have h73 : n = 2 * k₁^2 + 2 * k₂^2 := by linarith

        --Show 2 * k₁^2 + 2 * k₂^2 = (k₁ + k₂)^2 + (k₁ - k₂)^2.
        have h74 : 2 * k₁^2 + 2 * k₂^2 = (k₁ + k₂)^2 + (k₁ - k₂)^2 := by ring

        --Show n = (k₁ + k₂)^2 + (k₁ - k₂)^2
        have h75 : n = (k₁ + k₂)^2 + (k₁ - k₂)^2 := by linarith

        --Now 9k₁ + k₂), (k₁ - k₂) are witnesses; done.
        use (k₁ + k₂), (k₁ - k₂)

        --Case 2 : (Odd c ∧ Odd d)
        have h8 : (Odd c ∧ Odd d) := by tauto
        --obtain hk₁ and hk₂
        have : Odd c := by exact h8.1
        rcases this with ⟨k₁, hk₁⟩
        have : Odd d := by exact h8.2
        rcases this with ⟨k₂, hk₂⟩
        --Show 2 * n = (2 * k₁ + 1)^2 + (2 * k₂ + 1)^2.
        have h81 : 2 * n = (2 * k₁ + 1)^2 + (2 * k₂ + 1)^2 := by
            rw [hk₁, hk₂] at hcd
            exact hcd

        --Show (2 * k₁ + 1)^2 + (2 * k₂ + 1)^2 = 2 * (2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1).
        have h82 : (2 * k₁ + 1)^2 + (2 * k₂ + 1)^2 = 2 * (2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1) := by ring

        --Show n = 2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1.
        have h83 : n = 2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1 := by linarith

        --Show 2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1 = (k₁ + k₂ + 1)^2 + (k₁ - k₂)^2.
        have h84 : 2 * k₁^2 + 2 * k₂^2 + 2 * k₁ + 2 * k₂ + 1 = (k₁ + k₂ + 1)^2 + (k₁ - k₂)^2 := by ring

        --Show n = (k₁ + k₂ + 1)^2 + (k₁ - k₂)^2.
        have h85 : n = (k₁ + k₂ + 1)^2 + (k₁ - k₂)^2 := by linarith

        --Now (k₁ + k₂ + 1), (k₁ - k₂) are witnesses.
        use (k₁ + k₂ + 1), (k₁ - k₂)