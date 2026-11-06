import Mathlib


/-
Prove that there are positive integers  $a_1, a_2,\dots, a_{2020}$  such that  $$ \dfrac{1}{a_1}+\dfrac{1}{2a_2}+\dfrac{1}{3a_3}+\dots+\dfrac{1}{2020a_{2020}}=1. $$
-/

theorem number_theory_610 :
    ∃ a : ℕ → ℕ, (∀ i ∈ Finset.range 2020, a i > 0) ∧
    ∑ i ∈ Finset.range 2020, (1 / (i + 1 : ℚ)) * (1 / (a i : ℚ)) = 1 := by

  -- by induction
  have l_1 : ∀ n > 0, ∃ b : ℕ → ℕ, (∀ i ∈ Finset.range n, b i > 0) ∧
      ∑ i ∈ Finset.range n, (1 / (i + 1 : ℚ)) * (1 / (b i : ℚ)) = 1 := by

    intro n hn
    induction n with
    | zero => contradiction
    | succ n ih =>
      induction n with
      | zero =>
        simp
        use fun _ => 1
      | succ n _ =>

        -- If $\frac{1}{b_{1}} + \frac{1}{2b_{2}} + \dots + \frac{1}{n b_{n}} = 1$,
        obtain ⟨b, hb⟩ := ih (by linarith)

        -- take $a_1 = b_1, a_2 = b_2, \dots, a_{n - 1} = b_{n - 1}, a_n = (n + 1) b_{n}, a_{n + 1} = b_n$,
        set a : ℕ → ℕ := fun x =>
          if x < n then b x
          else (if x = n then (n + 1 + 1) * b n
          else (if x = (n + 1) then b n
          else 0))
          with ha
        use a

        -- prove that a is positive
        have t1 : ∀ i ∈ Finset.range (n + 1 + 1), a i > 0 := by
          intro i hi
          apply Finset.mem_range_succ_iff.mp at hi
          by_cases h : i < n
          . have t11 := hb.left i (by refine Finset.mem_range.mpr (by linarith))
            rw [show a i = b i by simp [ha, h]]
            exact t11
          . apply Nat.gt_of_not_le at h
            rcases (show i = n ∨ i = n + 1 by omega) with hv | hv
            <;> simp [ha, hv, hb]

        -- prove that $\frac{1}{b_{1}} + \frac{1}{2b_{2}} + \dots + \frac{1}{n b_{n}} + \frac{1}{(n + 1) a_{n + 1}} = 1$
        have t2 : ∑ i ∈ Finset.range (n + 1 + 1), 1 / ((i : ℚ) + 1) * (1 / (a i)) = 1 := by
          have t21 := hb.right
          rw [Finset.sum_range_succ] at t21
          have t22 : ∑ x ∈ Finset.range n, (1 / (x + 1) * (1 / (a x : ℚ))) = ∑ x ∈ Finset.range n, (1 / (x + 1 : ℚ) * (1 / (b x))) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [ha, List.mem_range.mp hi]
          have t23 : (1 : ℚ) / (n + 1) * (1 / (a n)) + 1 / ((n + 1) + 1) * (1 / (a (n + 1))) = 1 / (n + 1) * (1 / b n) := by
            rw [show a n = (n + 2) * b n by simp [ha], show a (n + 1) = b n by simp [ha]]
            norm_cast
            rw [Nat.cast_mul, Nat.cast_add, Nat.cast_add]
            repeat rw [mul_div, mul_one, div_div]
            have : (1:ℚ) / ((n + 2) * (b n)) = (n + 1) / ((n + 1) * ((↑n + ↑2) * (b n))) := by
              rw [show (2:ℚ) = 1 + 1 by norm_num, ← add_assoc]
              have hbnpos : b n > 0 := hb.left n (Finset.self_mem_range_succ n)
              apply (div_eq_div_iff ?_ ?_).mpr (by ring)
              any_goals
                norm_cast
                simp [Nat.not_eq_zero_of_lt hbnpos]
            norm_cast at this
            norm_cast
            rw [this, div_add_div_same, add_comm, mul_comm, mul_assoc, Nat.cast_mul, div_mul_eq_div_div]
            norm_cast
            rw [show n + 1 + 1 = n + 2 by ring, Nat.div_self hn, mul_comm]
            norm_cast
          rw [Finset.sum_range_succ, Finset.sum_range_succ, t22, add_assoc]
          norm_cast
          norm_cast at t23
          norm_cast at t21
          rw [t23, t21]
        exact ⟨t1, t2⟩

  -- specialize at 2020
  specialize l_1 2020 (by norm_num)
  obtain ⟨b, hb⟩ := l_1
  use b
