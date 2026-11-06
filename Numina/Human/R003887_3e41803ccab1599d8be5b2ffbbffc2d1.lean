import Mathlib

open Finset

/- 3. (10 points) $a_{1}, a_{2}, a_{3}, \cdots, a_{n}$ are natural numbers satisfying $0 < a_{1} < a_{2} < a_{3} \cdots < a_{n}$, and $\frac{13}{14}=\frac{1}{\mathrm{a}_{1}}, \frac{1}{\mathrm{a}_{2}}, \frac{1}{\mathrm{a}_{3}}+\cdots$ $+\frac{1}{a_{n}}$, then the minimum value of $n$ is . $\qquad$ -/
theorem number_theory_219381 :
    IsLeast {n | ∃ a : ℕ → ℕ, 0 < a 1 ∧ StrictMonoOn a (Icc 1 n)
      ∧ ∑ i ∈ Icc 1 n, (1 : ℚ) / a i = 13 / 14} 4 := by
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  · -- Show that a(1) = 1, a(2) = 3, a(3) = 11, a(4) = 231 satisfy all conditions.
    set a : ℕ → ℕ := fun i => if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 11 else 231
    use a
    constructorm* _ ∧ _
    -- 0 < 1 = a(1).
    · simp [a]
    -- a is strictly increasing on [1, 4].
    · apply strictMonoOn_of_lt_add_one
      · simp
        infer_instance
      simp
      intro i hi1 _ hi2
      interval_cases i <;> simp [a]
    -- 1 / a 1 + 1 / a 2 + 1 / a 3 + 1 / a 4 = 13 / 14.
    · simp [sum_Icc_succ_top, a]
      norm_num
  · intro n a ha0 ha h
    -- Assume that a is strictly increasing on [1, n], 0 < a 1, and
    -- ∑ i ∈ [1, n], 1 / a i = 13 / 14.
    -- Show that 4 ≤ n.
    -- First, prove that 1 ≤ n.
    have hn1 : 1 ≤ n := by
      -- If n = 0 then the sum is equal to 0.
      contrapose! h
      interval_cases n
      simp
      norm_num
    -- Assume that n < 4 and derive a contradiction.
    by_contra hn
    simp at hn
    -- Show that a 1 = 2.
    have ha1 : a 1 = 2 := by
      -- Assume that a 1 ≠ 2 and show that the sum is not equal to 13 / 14.
      contrapose! h
      -- Consider two cases a 1 = 1 or 3 ≤ a 1.
      cases' show a 1 = 1 ∨ 3 ≤ a 1 by omega with h h
      · -- If a 1 = 1 then the sum is greater than 1.
        rw [← add_sum_Ioc_eq_sum_Icc hn1, h]
        suffices 0 ≤ ∑ i ∈ Ioc 1 n, (1 : ℚ) / a i by linarith
        positivity
      · -- Suppose that 3 ≤ a 1.
        -- Consider all possible values of n: n = 1, n = 2, or n = 3.
        interval_cases n <;> simp only [Nat.reduceAdd, Nat.one_le_ofNat, sum_Icc_succ_top, Icc_self, sum_singleton]
        · -- If n = 1 then 1 / a 1 ≤ 1 / 3 < 13 / 14.
          qify at h
          apply ne_of_lt
          rw [div_lt_div_iff₀] <;> linarith
        · -- If n = 2 then 3 ≤ a 1 < a 2.
          have ha2 : 3 < a 2 := by
            apply lt_of_le_of_lt h
            apply ha <;> simp
          -- We get 1 / a 1 + 1 / a 2 ≤ 1 / 3 + 1 / 4 < 13 / 14.
          qify at h ha2
          field_simp
          nlinarith
        · -- If n = 3 then 3 ≤ a 1 < a 2 < a 3.
          -- So 4 ≤ a 2 and 5 ≤ a 3.
          have ha2 : 3 < a 2 := by
            apply lt_of_le_of_lt h
            apply ha <;> simp
          have ha3 : 4 < a 3 := by
            apply lt_of_le_of_lt (b := a 2) (by linarith)
            apply ha <;> simp
          replace ha2 : 4 ≤ a 2 := by linarith
          replace ha3 : 5 ≤ a 3 := by linarith
          qify at h ha2 ha3
          apply ne_of_lt
          -- We get 1 / a 1 + 1 / a 2 + 1 / a 3 ≤ 1 / 3 + 1 / 4 + 1 / 5 < 13 / 14.
          calc
            _ ≤ 1 / 3 + 1 / 4 + 1 / 5 := by gcongr
            _ < (13 : ℚ) / 14 := by norm_num
    -- Show that the sum is not equal to 13/14.
    contrapose! h
    -- Consider all possible values of n: n = 1, n = 2, or n = 3.
    interval_cases n <;> simp only [Nat.reduceAdd, Nat.one_le_ofNat, sum_Icc_succ_top, Icc_self, sum_singleton, ha1]
    · -- If n = 1 then 1 / 2 ≠ 13 / 14.
      norm_num
    · -- If n = 2 then 2 = a 1 < a 2, so 3 ≤ a 2.
      have ha2 : 3 ≤ a 2 := by
        suffices 2 < a 2 by linarith
        nth_rw 1 [← ha1]
        apply ha <;> simp
      apply ne_of_lt
      qify at ha2
      -- We get 1 / a 1 + 1 / a 2 ≤ 1 / 2 + 1 / 3 < 13/14.
      calc
        _ ≤ 1 / 2 + 1 / 3 := by gcongr
        _ < (13 : ℚ) / 14 := by norm_num
    · -- If n = 3 then 2 = a 1 < a 2 < a 3, so 3 ≤ a 2 and a 2 + 1 ≤ a 3.
      have ha2 : 3 ≤ a 2 := by
        suffices 2 < a 2 by linarith
        nth_rw 1 [← ha1]
        apply ha <;> simp
      have ha3 : a 2 + 1 ≤ a 3 := by apply ha <;> simp
      -- Consider two cases: 5 ≤ a 2 or a 2 < 5.
      by_cases ha2' : 5 ≤ a 2
      · apply ne_of_lt
        qify at ha2' ha3
        -- If 5 ≤ a 2 then 6 ≤ a 3 and we get
        -- 1 / a 1 + 1 / a 2 + 1 / a 3 ≤ 1 / 2 + 1 / 5 + 1 / 6 < 13/14.
        calc
          _ ≤ 1 / 2 + 1 / 5 + 1 / 6 := by
            gcongr
            linarith
          _ < (13 : ℚ) / 14 := by norm_num
      -- Assume now that 3 ≤ a 2 < 5.
      interval_cases a 2
      · -- If a 2 = 3 then 1 / a 3 = 2 / 21, or 2 * a 3 = 21, which is impossible.
        field_simp
        norm_cast
        omega
      · -- If a 2 = 4 then 1 / a 3 = 5 / 28, or 5 * a 3 = 28, which is impossible.
        field_simp
        norm_cast
        omega