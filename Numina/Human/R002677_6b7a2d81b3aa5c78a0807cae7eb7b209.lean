import Mathlib

--We prove that 3 is not a square of any natural number
lemma two_not_sq_nat : ¬ ∃ (n : ℕ), n ^ 2 = 3 := by
   rintro ⟨n, hn⟩
   have h1 : n ≤ 1 := by nlinarith
   interval_cases n <;> omega

--We prove that 33 is not a square of any natural number
lemma thirtythree_not_sq_nat : ¬ ∃ (n : ℕ), n ^ 2 = 33 := by
   rintro ⟨n, hn⟩
   have h1 : n ≤ 5 := by nlinarith
   interval_cases n <;> omega

--We prove (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5. The proof goes by induction on k.
lemma help  (k : ℕ) : (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5 = 0 := by
    refine Nat.dvd_iff_mod_eq_zero.mp ?_
    apply Finset.dvd_sum
    intro i ih
    induction' k with k hk
    simp at ih
    rw [ih]; decide
    have i1 : 5 ≤ i := by
        simp only [Finset.mem_Icc] at ih
        exact ih.1
    have i2 : i ≤ 5 + (k + 1) := by
        simp only [Finset.mem_Icc] at ih
        exact ih.2
    have i3 : i = 5 + (k + 1) ∨ i ≤ 5 + k := by omega
    rcases i3 with H|H
    rw [H]
    refine Nat.dvd_factorial ?_ ?_
    omega
    omega
    have i4 : i ∈ Finset.Icc 5 (5 + k) := by
        simp only [Finset.mem_Icc]
        exact ⟨i1, H⟩
    apply hk
    exact i4

--We prove a square modulo 5 is never 3.
lemma help1 (m : ℕ) : m^2 % 5 ≠ 3 := by
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega
    rcases h1 with (h | h | h | h | h) <;> simp [Nat.pow_mod, h]



/- 21. Determine the number of pairs of positive integers $n$ and $m$ such that

$$

1!+2!+3!+\cdots+n!=m^{2} \text {. }

$$
 -/
theorem number_theory_99019 :
    {(n, m) : ℕ × ℕ | n > 0 ∧ m > 0 ∧ ∑ i in Finset.Icc 1 n, Nat.factorial i = m^2}.ncard = 2 := by
        --We show that the given set is exactly {(1,1), (3,3)}.
        have H0 : {(n, m) : ℕ × ℕ | n > 0 ∧ m > 0 ∧ ∑ i in Finset.Icc 1 n, Nat.factorial i = m^2} = {(1,1), (3,3)} := by
            ext x
            constructor
            intro H
            obtain ⟨h1, h2, h⟩ := H
            set n := x.1
            set m := x.2
            --following cases are possible.
            have : n ≥ 4 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
            --show n ≠ 2
            have : n ≠ 2 := by
                intro h1
                rw [h1] at h
                have h12: ∑ i ∈ Finset.Icc 1 2, i.factorial = 3 := by decide
                rw [h12] at h
                apply two_not_sq_nat
                use m
                exact h.symm
            --show n is not ≥ 4.
            have : ¬ n ≥ 4 := by
                intro h1
                have : n = 4 ∨ n > 4 := by omega
                rcases this with H1|H1
                rw [H1] at h
                have : ∑ i ∈ Finset.Icc 1 4, i.factorial = 33 := by decide
                rw [this] at h
                apply thirtythree_not_sq_nat
                use m
                exact h.symm
                --Now n > 4.
                have hn : ∃ k, k ≥ 0 ∧ n = 5 + k := by
                    have h1 : n > 4 := H1
                    have h2 : n - 4 > 0 := by omega
                    use n - 5
                    constructor
                    · linarith
                    · omega
                obtain ⟨k, hk₁, hk₂⟩ := hn
                have h10 : ∑ i ∈ Finset.Icc 1 n, i.factorial = ∑ i ∈ Finset.Icc 1 4, i.factorial + ∑ i ∈ Finset.Icc 5 (5 + k), i.factorial := by
                    rw [hk₂]
                    -- Split the interval [1, 5 + k] into [1,4] and [5,5+k]
                    have : Finset.Icc 1 (5 + k) = Finset.Icc 1 4 ∪ Finset.Icc 5 (5 + k) := by
                        ext a
                        simp [Finset.mem_Icc, Finset.mem_union]
                        constructor
                        intro a_1
                        simp_all only [gt_iff_lt, ge_iff_le, false_or, true_or, ne_eq, zero_le, true_and, and_true,
                          add_pos_iff, Nat.ofNat_pos, n, m]
                        obtain ⟨fst, snd⟩ := x
                        obtain ⟨left, right⟩ := a_1
                        subst hk₂
                        simp_all only
                        omega
                        intro a_1
                        simp_all only [gt_iff_lt, ge_iff_le, false_or, true_or, ne_eq, zero_le, add_pos_iff,
                          Nat.ofNat_pos, n, m]
                        obtain ⟨fst, snd⟩ := x
                        subst hk₂
                        simp_all only
                        cases a_1 with
                        | inl h_1 =>
                          simp_all only [true_and]
                          obtain ⟨left, right⟩ := h_1
                          omega
                        | inr h_2 =>
                          simp_all only [and_true]
                          obtain ⟨left, right⟩ := h_2
                          omega
                    -- Rewrite the sum using this partition
                    rw [this, Finset.sum_union]

                    -- The two intervals are disjoint
                    apply Finset.disjoint_left.2
                    intro a ha
                    simp_all only [gt_iff_lt, ge_iff_le, false_or, true_or, ne_eq, zero_le, Finset.mem_Icc, not_and,
                      not_le, add_pos_iff, Nat.ofNat_pos, n, m]
                    intro a_1
                    obtain ⟨fst, snd⟩ := x
                    obtain ⟨left, right⟩ := ha
                    subst hk₂
                    simp_all only
                    omega

                --show (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5 = 0 .
                have h11 : (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5 = 0 := by
                    apply help
                --show (∑ i ∈ Finset.Icc 1 n, i.factorial) % 5 = ((∑ i ∈ Finset.Icc 1 4, i.factorial) % 5 + (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5) % 5.
                have h12 :  (∑ i ∈ Finset.Icc 1 n, i.factorial) % 5 = ((∑ i ∈ Finset.Icc 1 4, i.factorial) % 5 + (∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5) % 5 := by
                    have h121 : (∑ i ∈ Finset.Icc 1 n, i.factorial) % 5 = (∑ i ∈ Finset.Icc 1 4, i.factorial + ∑ i ∈ Finset.Icc 5 (5 + k), i.factorial) % 5 := by omega
                    rw [Nat.add_mod] at h121
                    exact h121
                rw [h11] at h12
                simp at h12
                have h13 : ∑ i ∈ Finset.Icc 1 4, i.factorial = 33 := by decide
                rw [h13] at h12
                rw [h] at h12
                simp at h12
                apply help1 m
                exact h12
            --hence n = 1 or n = 3.
            --so we do a case analysis.
            have : n = 1 ∨ n = 3 := by omega
            rcases this with H1|H1
            rw [H1] at h
            simp at h
            have : m = 1 := by exact Nat.eq_one_of_mul_eq_one_left (id (Eq.symm h))
            have : x = (1, 1) := by exact Prod.ext H1 this
            refine Set.mem_insert_iff.mpr ?_
            left
            exact this
            rw [H1] at h
            have : ∑ i ∈ Finset.Icc 1 3, i.factorial  = 9 := by decide
            rw [this] at h
            have : m = 3 := by
                have : m ≤ 3 := by nlinarith
                interval_cases m <;> omega
            have : x = (3, 3) := by exact Prod.ext H1 this
            refine Set.mem_insert_iff.mpr ?_
            right
            exact this
            intro H
            have H1 : x = (1, 1) ∨ x = (3, 3) := by exact H
            simp only [Set.mem_setOf_eq]
            rcases H1 with H2|H3
            · have H21 : x.1 = 1 := by rw [H2]
              have H22 : x.2 = 1 := by rw [H2]
              constructor
              omega
              constructor
              omega
              rw [H21, H22]
              norm_num
            · have H31 : x.1 = 3 := by rw [H3]
              have H32 : x.2 = 3 := by rw [H3]
              constructor
              omega
              constructor
              omega
              rw [H31, H32]
              norm_num
              decide
        rw [H0]
        rw [Set.ncard_eq_toFinset_card']
        rfl