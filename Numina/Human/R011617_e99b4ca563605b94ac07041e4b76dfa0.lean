import Mathlib

open Real

/- B1. Determine the exact upper bound of the sequence with the general term $a_{n}=n\left(\frac{20}{23}\right)^{n}$ for all $n \in \mathbb{N}$. -/
theorem algebra_135527 (a : ℕ → ℝ) (ha : ∀ n, a n = n * (20 / 23) ^ n) :
    IsGreatest { x | ∃ n : ℕ, x = a n} (7 * (20 / 23) ^ 7) := by
      --First we deterimine the range of n in which the sequence is increasing.
      have H0 : ∀ n ∈ Finset.Icc 0 6, a n < a 7 := by
        intro n H0
        rw [Finset.mem_Icc] at H0
        have H01 : 0 ≤ n := by exact H0.1
        have H02 : n ≤ 6 := by exact H0.2
        interval_cases n
        all_goals
        rw [ha, ha]
        norm_num
      have H1 : ∀ n ≥ 7 , a (n + 1) < a n := by
        by_contra H1
        push_neg at H1
        obtain ⟨n, hn1, hn2⟩ := H1
        have H2 : n > (20 / 3 : ℝ) := by
          have : 7 > ((20 / 3) : ℝ) := by norm_num
          rify at *
          linarith

        have H3 : (3 : ℝ) * n > (20 : ℝ) := by linarith
        have H4 : (23 : ℝ) * n > (20 : ℝ) * n + (20 : ℝ) := by linarith
        have H5 : (23 : ℝ) * n > (20 : ℝ) * (n + 1) := by linarith
        have H6 : n > ((20 / 23) : ℝ) * (n + 1) := by linarith
        have H7 : n * ((20 /23) : ℝ)^n > (20 / 23) * (n + 1) * ((20 / 23) : ℝ)^n := by
          norm_num
          exact H6
        have H8 : ((20 / 23) : ℝ) * (n + 1) * ((20 / 23) : ℝ)^n =  (n + 1) * ((20 / 23) : ℝ)^(n + 1) := by ring
        have H9 : n * ((20 /23) : ℝ)^n > (n + 1) * ((20 / 23) : ℝ)^(n + 1) := by linarith
        rw [ha, ha] at hn2
        push_cast at hn2
        linarith
      have H10 : ∀ n, a 7 ≥ a n := by
        intro n
        have : n < 7 ∨ n ≥ 7 := by omega
        rcases this with H11 | H11
        interval_cases n

        specialize H0 0
        have h0 : 0 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 h0)

        have h1 : 1 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 1 h1)

        have h2 : 2 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 2 h2)

        have h3 : 3 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 3 h3)

        have h4 : 4 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 4 h4)

        have h5 : 5 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 5 h5)

        have h6 : 6 ∈ Finset.Icc 0 6 := by exact Finset.insert_eq_self.mp rfl
        exact le_of_lt (H0 6 h6)

        induction n, H11 using Nat.le_induction
        case base => simp
        case succ n hn hmn => linarith [H1 n hn]


      unfold IsGreatest
      constructor
      refine Set.mem_setOf.mpr ?_
      use 7
      exact Eq.symm (ext_cauchy (congrArg cauchy (ha 7)))
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      specialize H10 n
      exact le_of_le_of_eq H10 (ha 7)