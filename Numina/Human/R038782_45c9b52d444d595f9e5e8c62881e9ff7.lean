import Mathlib

open Real

/-Let $a_{1}, a_{2}, a_{3}, a_{4}, a_{5}$ be real numbers whose sum is 20 . Determine with proof the smallest possible value of

$$
\sum_{1 \leq i< j \leq 5}\left\lfloor a_{i}+a_{j}\right\rfloor .
$$-/
theorem algebra_609136 :
  IsLeast {sum : ℤ | ∃ a : ℕ → ℝ, ∑ i ∈ Finset.Icc 1 5, a i = 20 ∧
    sum = ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, ⌊a i + a j⌋ } 72 := by

    have lem_fract_add_comm (a b : ℝ) : Int.fract (a + b) = Int.fract (b + a) := by
      congr 1
      ring

    -- We claim that the minimum is 72.

    constructor
    · simp
      -- 72 can be achieved by taking $a_{1}=a_{2}=a_{3}=$ $a_{4}=0.4$ and $a_{5}=18.4$.
      let a : ℕ → ℝ := fun a => match a with
      | 1 | 2 | 3 | 4 => 4 / 10
      | 5 => 184 / 10
      | _ => 0
      use a
      constructor
      ·
        iterate 4 rw [Finset.sum_Icc_succ_top]
        all_goals simp
        norm_num

      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp

      iterate 4 rw [Finset.sum_Ioc_succ_top]
      all_goals simp
      iterate 3 rw [Finset.sum_Ioc_succ_top]
      all_goals simp
      iterate 2 rw [Finset.sum_Ioc_succ_top]
      all_goals simp

      norm_num

    intro sum ⟨a, a_sum_20, h_sum⟩

    -- To prove that this is optimal, note that
    -- ∑ 1 ≤ i < j ≤ 5, ⌊a i + a j⌋ = ∑ 1 ≤ i < j ≤ 5, (a i + a j) - {a i + a j}
    have h_sum' : (sum : ℝ) = ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, ↑⌊a i + a j⌋ := by norm_cast
    have h_sum'' : (sum : ℝ) = ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, ((a i + a j) - Int.fract (a i + a j)) := by
      rw [h_sum']
      congr; ext; congr; ext
      unfold Int.fract
      ring

    -- ... = (∑ 1 ≤ i < j ≤ 5, (a i + a j)) - (∑ 1 ≤ i < j ≤ 5, {a i + a j})
    have : ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, ((a i + a j) - Int.fract (a i + a j)) =
      ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, (a i + a j) -
      ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, Int.fract (a i + a j) := by
      rw [← Finset.sum_sub_distrib]
      congr
      ext i
      exact Finset.sum_sub_distrib
    rw [this] at h_sum''

    -- notw that (∑ 1 ≤ i < j ≤ 5, (a i + a j)) = 80
    have : ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, (a i + a j) = 80 := by
      have : ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, (a i + a j) = 4 * ∑ i ∈ Finset.Icc 1 5, a i := by
        iterate 4 rw [Finset.sum_Icc_succ_top]
        all_goals simp
        iterate 4 rw [Finset.sum_Ioc_succ_top]
        all_goals simp
        iterate 3 rw [Finset.sum_Ioc_succ_top]
        all_goals simp
        iterate 2 rw [Finset.sum_Ioc_succ_top]
        all_goals simp
        iterate 4 rw [Finset.sum_Icc_succ_top]
        all_goals simp
        ring
      rw [this, a_sum_20]
      norm_num
    rw [this] at h_sum''

    -- so it suffices to maximize ∑ 1 ≤ i < j ≤ 5, {a i + a j}
    suffices h : (72 : ℝ) ≤ sum by norm_cast at h
    suffices h : ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, Int.fract (a i + a j) ≤ 8 by linarith

    -- where ∑ 1 ≤ i < j ≤ 5, {a i + a j} = (∑ 1 ≤ i ≤ 5, {a i + a (i + 2)}) + ∑ 1 ≤ i ≤ 5, {a i + a (i + 1)}
    have : ∑ i ∈ Finset.Icc 1 5, ∑ j ∈ Finset.Ioc i 5, Int.fract (a i + a j) =
      ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a ((i + 1) % 5 + 1)) +
      ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a (i % 5 + 1)) := by
      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp
      iterate 4 rw [Finset.sum_Ioc_succ_top]
      all_goals simp
      iterate 3 rw [Finset.sum_Ioc_succ_top]
      all_goals simp
      iterate 2 rw [Finset.sum_Ioc_succ_top]
      all_goals simp
      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp
      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp
      rw [
        lem_fract_add_comm (a 4) (a 1),
        lem_fract_add_comm (a 5) (a 2),
        lem_fract_add_comm (a 5) (a 1),
      ]
      ring
    rw [this]

    simp

    -- we need the fact that {a} + {b} = {a + b} - z for some integer z
    have lem_fract_add (a b : ℝ) : ∃ z : ℤ, Int.fract a + Int.fract b = Int.fract (a + b) - z := by
      have ⟨z, hz⟩ := Int.fract_add a b
      use z
      linarith [hz]

    -- taking each sum modulo 1,
    -- we get that ∑ 1 ≤ i ≤ 5, {a i + a (i + 2)} is an integer
    have h_rhs_1_int: ∃ n : ℤ, n = ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a ((i + 1) % 5 + 1)) := by
      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp

      have ⟨z1, h1⟩ := lem_fract_add (a 1 + a 3) (a 2 + a 4)
      rw [h1]
      have ⟨z2, h2⟩ := lem_fract_add (a 4 + a 1) (a 5 + a 2)
      rw [add_assoc, h2, add_sub]
      rw [sub_add_eq_add_sub, sub_add_eq_add_sub]
      have ⟨z3, h3⟩ := lem_fract_add (a 1 + a 3 + (a 2 + a 4)) (a 3 + a 5)
      rw [h3, sub_add_eq_add_sub]
      have ⟨z4, h4⟩ := lem_fract_add (a 1 + a 3 + (a 2 + a 4) + (a 3 + a 5)) (a 4 + a 1 + (a 5 + a 2))
      rw [h4]

      have : (a 1 + a 3 + (a 2 + a 4) + (a 3 + a 5) + (a 4 + a 1 + (a 5 + a 2))) = 2 * ∑ i ∈ Finset.Icc 1 5, a i := by
        iterate 4 rw [Finset.sum_Icc_succ_top]
        all_goals simp
        ring
      rw [this, a_sum_20]
      norm_num
      norm_cast
      simp

    -- let n₁ be the integer ∑ 1 ≤ i ≤ 5, {a i + a (i + 2)}
    have ⟨n₁, hn₁⟩ := h_rhs_1_int
    rw [← hn₁]

    -- we have ∑ 1 ≤ i ≤ 5, {a i + a (i + 2)} < 5 as each summand < 1
    have h_rhs_1_le : ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a ((i + 1) % 5 + 1)) < 5 := by
      apply lt_of_lt_of_le (b := ∑ i ∈ Finset.Icc 1 5, 1)
      · apply Finset.sum_lt_sum
        · intro i _
          apply le_of_lt
          exact Int.fract_lt_one (a i + a ((i + 1) % 5 + 1))
        use 1
        simp;
        exact Int.fract_lt_one (a 1 + a 3)
      rw [Finset.sum_const]
      simp

    -- so n₁ < 5, and n₁ ≤ 4
    have : n₁ < 5 := by
      suffices h : (n₁ : ℝ) < 5 by norm_cast at h
      exact lt_of_eq_of_lt hn₁ h_rhs_1_le
    have : n₁ ≤ 4 := by exact Int.lt_add_one_iff.mp this

    -- similarly, ∑ 1 ≤ i ≤ 5, {a i + a (i + 1)} is an integer
    have h_rhs_2_int : ∃ n : ℤ, n = ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a (i % 5 + 1)) := by
      iterate 4 rw [Finset.sum_Icc_succ_top]
      all_goals simp

      have ⟨z1, h1⟩ := lem_fract_add (a 1 + a 2) (a 2 + a 3)
      rw [h1]
      have ⟨z2, h2⟩ := lem_fract_add (a 4 + a 5) (a 5 + a 1)
      rw [add_assoc, h2, add_sub]
      rw [sub_add_eq_add_sub, sub_add_eq_add_sub]
      have ⟨z3, h3⟩ := lem_fract_add (a 1 + a 2 + (a 2 + a 3)) (a 3 + a 4)
      rw [h3, sub_add_eq_add_sub]
      have ⟨z4, h4⟩ := lem_fract_add (a 1 + a 2 + (a 2 + a 3) + (a 3 + a 4)) (a 4 + a 5 + (a 5 + a 1))
      rw [h4]

      have : (a 1 + a 2 + (a 2 + a 3) + (a 3 + a 4) + (a 4 + a 5 + (a 5 + a 1))) = 2 * ∑ i ∈ Finset.Icc 1 5, a i := by
        iterate 4 rw [Finset.sum_Icc_succ_top]
        all_goals simp
        ring
      rw [this, a_sum_20]
      norm_num
      norm_cast
      simp

    -- let n₂ be the integer ∑ 1 ≤ i ≤ 5, {a i + a (i + 1)}
    have ⟨n₂, hn₂⟩ := h_rhs_2_int
    rw [← hn₂]

    -- we have ∑ 1 ≤ i ≤ 5, {a i + a (i + 1)} < 5 as each summand < 1
    have h_rhs_2_le : ∑ i ∈ Finset.Icc 1 5, Int.fract (a i + a (i % 5 + 1)) < 5 := by
      apply lt_of_lt_of_le (b := ∑ i ∈ Finset.Icc 1 5, 1)
      · apply Finset.sum_lt_sum
        · intro i _
          apply le_of_lt
          exact Int.fract_lt_one (a i + a (i % 5 + 1))
        use 1
        simp;
        exact Int.fract_lt_one (a 1 + a 2)
      rw [Finset.sum_const]
      simp

    -- so n₁ < 5, and n₁ ≤ 4
    have : n₂ < 5 := by
      suffices h : (n₂ : ℝ) < 5 by norm_cast at h
      exact lt_of_eq_of_lt hn₂ h_rhs_2_le
    have : n₂ ≤ 4 := by exact Int.lt_add_one_iff.mp this

    -- now the goal is to maximize n₁ + n₂ ≤ 4 + 4 = 8, we are done
    norm_cast
    linarith
