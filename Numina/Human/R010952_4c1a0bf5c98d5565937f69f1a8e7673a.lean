import Mathlib

/- $6 \cdot 38$ Given that the function $f(x)$ is defined over the entire real line, and when its graph is rotated by $\frac{\pi}{2}$ about the origin, it remains unchanged.
(1) Prove that the equation $f(x)=x$ has exactly one solution.
(2) Provide an example of such a function. -/
theorem algebra_206433 {p : (ℝ → ℝ) → Prop}
  (hp : ∀ f, p f = ∀ x y, f x = y → f (-y) = x)
  : (∀ f, p f → ∃! x, f x = x) ∧ ∃ f, p f
  := by
    constructor
    -- first we prove that every such function has a unique fixed point
    · intro f h
      rw [hp] at h
      refine ⟨0, ?_⟩
      -- let a = f 0
      let a := f 0
      -- then f (-a) = 0
      have app := h 0 a rfl
      -- so f (-0) = -a
      have f_zero : f (-0) = -a := h _ _ app

      -- but then f 0 = -f 0
      simp only [neg_zero, a] at f_zero

      -- so f 0 = 0
      have f_zero_eq_zero : f 0 = 0 := by linarith

      -- then we just need to prove that it's unique
      refine ⟨f_zero_eq_zero, ?_⟩
      -- let us have f x0 = x0, for som x0
      intro x0 xh
      -- then f (-x0) = x0
      have f_x0 : f (-x0) = x0 := h _ _ xh

      -- so f (-x0) = -x0
      have f_x0_2 : f (-x0) = -x0 := h _ _ f_x0

      -- which means x0 = -x0
      rw [f_x0] at f_x0_2
      -- so x0 = 0
      linarith only [f_x0_2]
    -- we give an example of such a function
    · let f : ℝ → ℝ := by
        intro x
        by_cases x = 0
        -- f 0 = 0
        · exact 0
        · by_cases ∃ k : ℤ, |x| ∈ Set.Ico (4 ^ k) (2 * 4 ^ k)
          -- f x = -x / 2 when 4 ^ k ≤ |x| ≤ 2 * 4 ^ k (k ∈ Z)
          · exact -(x / 2)
          -- else f x = 2 * x
          · exact 2 * x
      -- then we just have to prove that the function remains unchanged when rotated
      refine ⟨f, ?_⟩
      rw [hp]

      intro x y fh
      -- given f x = y, we'll prove that f (-y) = x
      unfold f at fh ⊢
      rw [abs_neg]
      simp only [neg_eq_zero, abs_neg, mul_neg, dite_eq_ite] at fh ⊢
      -- we consider cases of f x
      split_ifs at fh with h1 h2
      -- if x = 0, then y = 0
      · subst h1 fh
        simp only [↓reduceIte]
      -- let us have 4 ^ k ≤ |x| ≤ 2 * 4 ^ k (k ∈ Z)
      · subst fh
        simp only [neg_eq_zero, div_eq_zero_iff, h1, OfNat.ofNat_ne_zero, or_self, ↓reduceIte,
          abs_neg, Set.mem_Ico, neg_neg, mul_neg]
        -- consider cases of f (-y)
        split_ifs with h3
        -- if we have 4 ^ k ≤ |-x / 2| ≤ 2 * 4 ^ k (k ∈ Z), then we'll have a contradiction
        · have abs_eq : |(-(x / 2))| = (1 / 2) * |x| := by
            simp only [abs_neg, one_div, abs_div, Nat.abs_ofNat]
            ring
          rw [abs_eq] at h3
          obtain ⟨k1, kh1⟩ := h2
          obtain ⟨k2, kh2⟩ := h3

          -- express |-x / 2| range as |x| range
          have mem_mul_two : |x| ∈ Set.Ico ((4 ^ k2) * 2) ((2 * 4 ^ k2) * 2) := by
            simp only [one_div, div_inv_eq_mul, Set.mem_Ico]
            simp only [one_div, Set.mem_Ico] at kh2
            constructor
            · linarith only [kh2.1]
            · linarith only [kh2.2]

          -- multiplying endpoints of our intervals with 2 gives us disjoint intervals
          have disj : Disjoint (Set.Ico (4 ^ k1) (2 * 4 ^ k1) : Set ℝ) (Set.Ico (4 ^ k2 * 2) (2 * 4 ^ k2 * 2)) := by
            rw [Set.Ico_disjoint_Ico]
            -- prove for cases of k1 ≤ k2
            by_cases hk : k1 ≤ k2
            · have rhs : (4 ^ k1 : ℝ) ≤ 4 ^ k2 * 2 := by
                rw [←mul_one ((4 : ℝ) ^ k1)]
                gcongr
                norm_num
                norm_num
              simp only [rhs, sup_of_le_right, inf_le_iff, Nat.ofNat_pos, mul_le_mul_right]

              refine Or.inl ?_
              rw [mul_comm]
              simp only [Nat.ofNat_pos, mul_le_mul_right, Nat.one_lt_ofNat, zpow_le_zpow_iff_right₀]
              exact hk
            · rw [not_le] at hk

              have four_not_zero : (4 : ℝ) ≠ 0 := by norm_num

              have lee : (4 : ℝ) ^ k2 * 4 ≤ 4 ^ k1 := by
                have k1_eq : k1 = (k1 - 1) + 1 := (Int.sub_add_cancel k1 1).symm
                rw [k1_eq, zpow_add₀ four_not_zero]
                gcongr
                · linarith only
                · linarith only [hk]
                · norm_num

              have rhs_le : (4 : ℝ) ^ k2 * 2 ≤ (4 : ℝ) ^ k1 := by
                refine le_trans ?_ lee
                gcongr
                linarith only
              simp only [rhs_le, sup_of_le_left, inf_le_iff]
              refine Or.inr ?_
              ring_nf
              exact lee

          -- but then we have that |x| is contained in two disjoint sets
          have mems := Disjoint.ne_of_mem disj kh1 mem_mul_two

          -- contradiction
          contradiction
        -- the case 2 * (x / 2) = x is valid
        · ring
      -- now we don't have 4 ^ k ≤ |x| ≤ 2 * 4 ^ k, for any k
      · subst fh
        simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, h1, ↓reduceIte]
        split_ifs with h3
        -- the case -(-(2 * x) / 2) = x is valid
        · ring
        -- now we don't have we don't have 4 ^ k ≤ |2 * x| ≤ 2 * 4 ^ k, for any k either
        · simp only [not_exists] at h2 h3

          -- There is a set of intervals which |x| is not a member of
          have not_mem_intervals_1 : |x| ∉ Set.iUnion (fun z : ℤ => (Set.Ico (4 ^ z) (2 * 4 ^ z))) := by
            simp only [Set.mem_iUnion, not_exists]
            exact h2

          -- There is also an offset set of intervals which |x| is not a member of
          have not_mem_intervals_2 : |x| ∉ Set.iUnion (fun z : ℤ => Set.Ico (2 * 4 ^ z) (4 ^ (z + 1))) := by
            simp only [Set.mem_iUnion, not_exists]
            intro z
            have mul_two_not_mem := h3 (z + 1)
            convert_to |2 * x| ∉ Set.Ico (2 * (2 * 4 ^ z)) (2 * 4 ^ (z + 1)) using 3 at mul_two_not_mem
            · have four_ne_zero : (4 : ℝ) ≠ 0 := by norm_num
              rw [zpow_add₀ four_ne_zero]
              ring
            have abs_mul : |2 * x| = 2 * |x| := by rw [abs_mul, Nat.abs_ofNat]

            have f_inj : (fun x : ℝ => 2 * x).Injective := mul_right_injective₀ (by norm_num)
            rwa [abs_mul, ←Set.image_mul_left_Ico (by positivity), f_inj.mem_set_image] at mul_two_not_mem

          -- combine the two types of intervals into one set of intervals
          have intervals_union : Set.iUnion (fun z : ℤ => (Set.Ico (4 ^ z) (2 * 4 ^ z)))
            ∪ Set.iUnion (fun z : ℤ => Set.Ico (2 * 4 ^ z) (4 ^ (z + 1))) = (Set.iUnion (fun z : ℤ => Set.Ico (4 ^ z) (4 ^ (z + 1))) : Set ℝ) := by
              rw [←Set.iUnion_union_distrib]
              apply Set.iUnion_congr
              intro z
              apply Set.Ico_union_Ico_eq_Ico
              · have pos : 0 ≤ (4 : ℝ) ^ z := by positivity
                linarith
              have four_not_zero : (4 : ℝ) ≠ 0 := by norm_num
              rw [zpow_add₀ four_not_zero, mul_comm]
              gcongr
              · linarith only

          -- the two sets of intervals cover every positive number
          have intervals_eq_pos : Set.iUnion (fun z : ℤ => Set.Ico (4 ^ z) (4 ^ (z + 1))) = Set.Ioi (0 : ℝ) := by
            ext i
            simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ioi]
            constructor
            -- intervals are positive
            · intro ⟨z, h1, h2⟩
              refine lt_of_lt_of_le ?_ h1
              positivity
            -- positive number is in some interval
            · intro aa
              -- it's in the interval with index log_4(i)
              refine ⟨Int.log 4 i, ?_⟩
              constructor
              -- larger than or equal to the lower bound
              · apply Int.zpow_log_le_self
                norm_num
                exact aa
              -- smaller than the upper bound
              · apply Int.lt_zpow_succ_log_self
                norm_num

          -- so |x| is not positive
          have abs_not_mem : |x| ∉ Set.Ioi 0 := by
            rw [←intervals_eq_pos, ←intervals_union, Set.mem_union, or_iff_not_and_not, not_not]
            exact ⟨not_mem_intervals_1, not_mem_intervals_2⟩

          -- but then x = 0
          simp only [Set.mem_Ioi, abs_pos, ne_eq, Decidable.not_not] at abs_not_mem

          -- but we're in a case when x ≠ 0, contradiction
          contradiction