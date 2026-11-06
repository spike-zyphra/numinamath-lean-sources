import Mathlib

set_option maxHeartbeats 500000

/-Let $x$ and $y$ be non-negative real numbers that sum to 1 . Compute the number of ordered pairs $(a, b)$ with $a, b \in\{0,1,2,3,4\}$ such that the expression $x^{a} y^{b}+y^{a} x^{b}$ has maximum value $2^{1-a-b}$.-/
theorem algebra_610248 :
  {(a, b) : ℕ × ℕ | a ≤ 4 ∧ b ≤ 4 ∧
    IsGreatest
      {f : ℝ | ∃ x y : ℝ, f = x^a * y^b + y^a * x^b ∧ x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1}
      ((2 : ℝ) ^ (1 - a - b : ℝ))
  }.encard = 17 := by

  -- Denote S the set of feasible pairs (a, b)
  let S := {(a, b) : ℕ × ℕ | a ≤ 4 ∧ b ≤ 4 ∧
    IsGreatest
      {f : ℝ | ∃ x y : ℝ, f = x^a * y^b + y^a * x^b ∧ x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1}
      ((2 : ℝ) ^ (1 - a - b : ℝ))}

  -- Denote Δ the set of x, y such that x + y = 1
  let Δ := {(x, y) : ℝ × ℝ | x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1}

  -- Denote F a b the set of values of x^a * y^b + y^a * x^b for x + y = 1
  let F := fun (a b : ℕ) ↦ {f : ℝ | ∃ x y : ℝ, f = x^a * y^b + y^a * x^b ∧ x ≥ 0 ∧ y ≥ 0 ∧ x + y = 1}

  --  Let f(x, y)=x^a y^b+y^a x^b. Observe that 2^(1-a-b) is merely the value of f(1/2, 1/2),
  -- so this value is always achievable.
  have h_max_mem (a b : ℕ) : ((2 : ℝ) ^ (1 - a - b : ℝ)) ∈ F a b := by
    use (1 / 2), (1 / 2)
    field_simp
    constructor
    · rw [← pow_add]
      rw [show (2 : ℝ) ^ (a + b) = 2 ^ (a + b : ℝ) by norm_cast]
      rw [← Real.rpow_add]
      simp
      all_goals norm_num
    norm_num

  -- Then the condition that x^a * y^b + y^a * x^b has maximum value 2^(1-a-b) is equivalent to that
  -- x^a * y^b + y^a * x^b ≤ 2^(1-a-b) for all x ∈ Δ
  have h_max_iff_le (a b : ℕ) : IsGreatest (F a b) ((2 : ℝ) ^ (1 - a - b : ℝ)) ↔
    ∀ (x y : ℝ), ⟨x, y⟩ ∈ Δ → x^a * y^b + y^a * x^b ≤ ((2 : ℝ) ^ (1 - a - b : ℝ)) := by
    constructor
    · intro ⟨_, h_ub⟩
      intro x y ⟨x_nonneg, y_nonneg, xy_sum_1⟩
      have : x ^ a * y ^ b + y ^ a * x ^ b ∈ F a b := by use x, y
      exact h_ub this
    · intro h_le
      constructor
      · exact h_max_mem a b
      rintro _ ⟨x, y, rfl, h_xy_Δ⟩
      apply h_le
      exact h_xy_Δ

  -- We claim that if (a, b) satisfies the condition, so does (a+1, b+1).
  -- To see this, observe that if f(x, y) ≤ 2^(1-a-b)$, then multiplying by the inequality x * y ≤ 1/4
  -- yields x^{a+1} y^{b+1}+$ $y^{a+1} x^{b+1} ≤ 2^{-1-a-b}, as desired.
  have h_succ_mem_S_of_mem_S {a b : ℕ} (h_mem : ⟨a, b⟩ ∈ S) (ha : a + 1 ≤ 4) (hb : b + 1 ≤ 4):
    ⟨a + 1, b + 1⟩ ∈ S := by
      use ha, hb
      have ⟨_, _, h_max⟩:= h_mem
      rw [h_max_iff_le] at h_max ⊢
      intro x y ⟨x_nonnge, y_nonneg, xy_sum⟩
      have h_le' := h_max x y ⟨x_nonnge, y_nonneg, xy_sum⟩

      have : x ^ (a + 1) * y ^ (b + 1) + y ^ (a + 1) * x ^ (b + 1) = x * y * (x ^ a * y ^ b + y ^ a * x ^ b) := by ring
      rw [this]

      have : 2 ^ (1 - ↑(a + 1) - ↑(b + 1) : ℝ) = (1 / 4 : ℝ) * 2 ^ (1 - ↑a - ↑b : ℝ) := by
        field_simp
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by ring, ← Real.rpow_add]
        congr 1
        ring
        norm_num
      rw [this]
      gcongr
      · suffices h : 4 * x * y ≤ 1 by linarith
        trans (x + y) ^ 2
        · apply le_of_sub_nonneg
          rw [show (x + y) ^ 2 - 4 * x * y = (x - y) ^ 2 by ring]
          positivity
        rw [xy_sum, one_pow]

  -- We also have by symmetry that if (a, b) satisfy the condition then so does (b, a).
  have h_mem_S_comm {a b : ℕ} (h_mem : (a, b) ∈ S) : (b, a) ∈ S := by
    have ⟨ha, hb, h_max⟩:= h_mem
    use hb, ha
    rw [h_max_iff_le] at h_max ⊢
    intro x y h_Δ
    have := h_max x y h_Δ
    rw [add_comm, mul_comm]
    nth_rw 2 [mul_comm]
    rw [show (1 - b - a : ℝ) = (1 - a - b) by ring]
    exact this

  -- If a=b=0, then f(x, y)=2, so (0,0) works.
  have h_0_0_mem : ⟨0, 0⟩ ∈ S := by
    use (by norm_num)
    use (by norm_num)
    rw [h_max_iff_le]
    simp
    intros
    norm_num

  -- If a=1 and b=0, then f(x, y)=x+y=1, so (1,0) works
  have h_1_0_mem : ⟨1, 0⟩ ∈ S := by
    use (by norm_num)
    use (by norm_num)
    rw [h_max_iff_le]
    simp
    rintro _ _ ⟨_, _, h⟩
    rw [h]

  -- If a=3 and b=1, then f(x, y) = x*y(x^2+y^2)= x * y(1-2 * x * y), which is maximized at x * y = 1/4 ↔ x = y = 1/2,
  -- so (3,1) works.
  have h_3_1_mem : ⟨3, 1⟩ ∈ S := by
    use (by norm_num)
    use (by norm_num)
    rw [h_max_iff_le]
    simp
    rintro x y ⟨_, _, xy_sum⟩
    rw [show x ^ 3 * y + y ^ 3 * x = x * y * (x ^ 2 + y ^ 2) by ring]
    have : x ^ 2 + y ^ 2 = 1 - 2 * (x * y) := by
      suffices h : (x + y) ^ 2 = 1 by rw [add_pow_two] at h; linarith
      rw [xy_sum, one_pow]
    rw [this]
    generalize x * y = a
    have : a * (1 - 2 * a) = -2 * (a - 1 / 4 : ℝ) ^ 2 + 2 ^ (-3 : ℝ) := by ring
    rw [this]
    simp
    positivity

  -- For a ≥ 2, (a, 0) fails since f(1,0)=1 > 2^(1-a)
  have h_2_0_notin : ⟨2, 0⟩ ∉ S := by
    intro ⟨_, _, h_max⟩
    rw [h_max_iff_le] at h_max
    simp at h_max
    have := h_max 1 0 (show ⟨1, 0⟩ ∈ Δ by repeat use (by norm_num))
    norm_num at this

  have h_3_0_notin : ⟨3, 0⟩ ∉ S := by
    intro ⟨_, _, h_max⟩
    rw [h_max_iff_le] at h_max
    simp at h_max
    have := h_max 1 0 (show ⟨1, 0⟩ ∈ Δ by repeat use (by norm_num))
    norm_num at this

  have h_4_0_notin : ⟨4, 0⟩ ∉ S := by
    intro ⟨_, _, h_max⟩
    rw [h_max_iff_le] at h_max
    simp at h_max
    have := h_max 1 0 (show ⟨1, 0⟩ ∈ Δ by repeat use (by norm_num))
    norm_num at this

  -- However, if a=4 and b=1, then
  -- f(x, y) = x*y * (x^3 + y^3) = (x * y) * ((x+y)^3 - 3 * x * y * (x+y)) = x * y * (1 - 3 * x * y),
  -- which is maximized at x * y = 1 / 6. Thus (4,1) does not work.
  have h_4_1_notin : ⟨4, 1⟩ ∉ S := by
    intro ⟨_, _, h_max⟩
    rw [h_max_iff_le] at h_max
    simp at h_max

    have ⟨x, y, xy_mem, h_xy⟩ : ∃ x y : ℝ, ⟨x, y⟩ ∈ Δ ∧ x * y = 1 / 6 := by
      use ((3 - √3) / 6), ((3 + √3) / 6)
      constructor
      · constructor
        · apply div_nonneg
          simp
          refine Real.sqrt_le_iff.mpr ?h.left.left.ha.a
          repeat use (by norm_num)
        constructor
        · positivity
        ring
      field_simp
      have : (3 - √3) * (3 + √3) = 9 - √3 ^ 2 := by ring
      rw [this]
      rw [Real.sq_sqrt]
      repeat norm_num

    have := h_max x y xy_mem
    rw [show x ^ 4 * y + y ^ 4 * x = (x * y) * ((x + y) ^ 3 - 3 * (x * y) * (x + y)) by ring] at this
    rw [xy_mem.2.2, h_xy] at this
    norm_num at this

  -- by symmetry we deduce that (0, 2), (0, 3), (0, 4), (1, 4) all do not work
  have h_notin_S_comm {a b : ℕ} (h_notin : (a, b) ∉ S) : (b, a) ∉ S := by
    intro h
    have := h_mem_S_comm h
    contradiction

  have h_0_2_notin : ⟨0, 2⟩ ∉ S := h_notin_S_comm h_2_0_notin
  have h_0_3_notin : ⟨0, 3⟩ ∉ S := h_notin_S_comm h_3_0_notin
  have h_0_4_notin : ⟨0, 4⟩ ∉ S := h_notin_S_comm h_4_0_notin
  have h_1_4_notin : ⟨1, 4⟩ ∉ S := h_notin_S_comm h_4_1_notin

  -- From these results, we are able to deduce all the pairs that do work
  have : S = ({
    ⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩, ⟨4, 4⟩,
    ⟨1, 0⟩, ⟨2, 1⟩, ⟨3, 2⟩, ⟨4, 3⟩,
    ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩,
    ⟨3, 1⟩, ⟨4, 2⟩, ⟨2, 4⟩, ⟨1, 3⟩
  } : Finset (ℕ × ℕ)) := by
    ext ⟨a, b⟩
    constructor
    · intro h_mem
      norm_cast
      have ⟨_, _, _⟩:= h_mem
      interval_cases a
      · interval_cases b
        · simp
        · simp
        · exfalso; exact h_0_2_notin h_mem
        · exfalso; exact h_0_3_notin h_mem
        · exfalso; exact h_0_4_notin h_mem
      · interval_cases b
        on_goal -1 => exfalso; exact h_1_4_notin h_mem
        all_goals simp
      · interval_cases b
        · exfalso; exact h_2_0_notin h_mem
        all_goals simp
      · interval_cases b
        · exfalso; exact h_3_0_notin h_mem
        all_goals simp
      · interval_cases b
        · exfalso; exact h_4_0_notin h_mem
        · exfalso; exact h_4_1_notin h_mem
        all_goals simp
    · intro ab_mem
      norm_cast at ab_mem
      fin_cases ab_mem
      · exact h_0_0_mem
      · exact h_succ_mem_S_of_mem_S h_0_0_mem (by norm_num) (by norm_num)
      · iterate 2 apply h_succ_mem_S_of_mem_S
        exact h_0_0_mem
        all_goals norm_num
      · iterate 3 apply h_succ_mem_S_of_mem_S
        exact h_0_0_mem
        all_goals norm_num
      · iterate 4 apply h_succ_mem_S_of_mem_S
        exact h_0_0_mem
        all_goals norm_num
      · exact h_1_0_mem
      · iterate 1 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · iterate 2 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · iterate 3 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · apply h_mem_S_comm
        exact h_1_0_mem
      · apply h_mem_S_comm
        iterate 1 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · apply h_mem_S_comm
        iterate 2 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · apply h_mem_S_comm
        iterate 3 apply h_succ_mem_S_of_mem_S
        exact h_1_0_mem
        all_goals norm_num
      · exact h_3_1_mem
      · apply h_succ_mem_S_of_mem_S
        exact h_3_1_mem
        all_goals norm_num
      · apply h_succ_mem_S_of_mem_S
        apply h_mem_S_comm
        exact h_3_1_mem
        all_goals norm_num
      · apply h_mem_S_comm
        exact h_3_1_mem

  unfold S at this
  rw [this]
  rw [Set.encard_eq_coe_toFinset_card]
  rfl
