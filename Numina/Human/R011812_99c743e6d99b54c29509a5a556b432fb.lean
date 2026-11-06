import Mathlib

open scoped BigOperators

/-this lemma is copied from newer version of mathlib-/
lemma rpow_right_inj {x y z : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_lt with h | h
  · exact (Real.strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (Real.strictMono_rpow_of_base_gt_one h).injective H

/-6. [5] We say " $s$ grows to $r$ " if there exists some integer $n>0$ such that $s^{n}=r$. Call a real number $r$ "sparse" if there are only finitely many real numbers $s$ that grow to $r$. Find all real numbers that are sparse.-/
theorem algebra_154490 :
  {r : ℝ | {s : ℝ | ∃ n : ℕ, 0 < n ∧ s ^ n = r}.Finite} = {-1, 0, 1} := by

    ext r
    constructor
    · by_contra! h
      -- for any number r other than -1, 0, 1, we show r is not sparse
      obtain ⟨h_r_sparse, r_notin⟩ := h
      simp at h_r_sparse r_notin

      -- let S be the set of s that s grows to r, we will prove S is infinite
      let S := {s : ℝ | ∃ n : ℕ, 0 < n ∧ s ^ n = r}

      by_cases hr : r > 0
      · -- if r > 0, then r ≠ 1, so r, r^(1/3), r^(1/5) ... all grows to r
        let f : ℕ → ℝ := fun n ↦ r ^ ((1 : ℝ) / (2 * n + 1))

        -- indeed, r^(1/2n+1) ∈ S for all n
        have h_f_to_sparse : ∀ n, f n ∈ S := by
          intro n
          use 2 * n + 1
          constructor
          · positivity
          unfold f

          have : (r ^ ((1 : ℝ) / (2 * ↑n + 1))) ^ (2 * n + 1) =
            (r ^ ((1 : ℝ) / (2 * ↑n + 1))) ^ (↑(2 * n + 1) : ℝ) := by
              exact Eq.symm (Real.rpow_natCast (r ^ ((1 : ℝ) / (2 * n + 1))) (2 * n + 1))
          rw [this]

          rw [← Real.rpow_mul]
          field_simp
          positivity

        -- moreover, n ↦ r^(1/2n+1) is injective from ℕ to S
        have h_f_inj : Function.Injective f := by
          intro n m h_eq
          unfold f at h_eq
          have rpos : r > 0 := by linarith
          have r_ne: r ≠ 1 := by exact fun h ↦ r_notin.2.2 h
          apply (rpow_right_inj rpos r_ne |>.mp) at h_eq
          field_simp at h_eq
          symm; exact h_eq

        -- therefore S is infinite
        have : S.Infinite := by
          refine Set.infinite_of_injective_forall_mem (α := ℕ) (f := f) ?_ ?_
          all_goals assumption

        contradiction

      · -- if r ≤ 0 then r < 0 as r ≠ 0
        have : r ≠ 0 := r_notin.2.1
        have : r < 0 := by
          push_neg at hr
          exact lt_of_le_of_ne hr this

        -- we show that -1 * -r, -1 * (-r)^(1/3), -1 * (-r)^(1/5) ... all grows to r
        let f : ℕ → ℝ := fun n ↦ -1 * (-r) ^ ((1 : ℝ) / (2 * n + 1))

        -- -1 * (-r)^(1/(2n + 1)) ∈ S for all n
        have h_f_to_sparse : ∀ n, f n ∈ S := by
          intro n
          use 2 * n + 1
          constructor
          · positivity
          unfold f

          rw [mul_pow]
          rw [Odd.neg_one_pow (by simp only [even_two, Even.mul_right, Even.add_one])]

          have : ((-r) ^ ((1 : ℝ) / (2 * ↑n + 1))) ^ (2 * n + 1) =
            ((-r) ^ ((1 : ℝ) / (2 * ↑n + 1))) ^ (↑(2 * n + 1) : ℝ) := by
              exact Eq.symm (Real.rpow_natCast ((-r) ^ ((1 : ℝ) / (2 * n + 1))) (2 * n + 1))
          rw [this]

          rw [← Real.rpow_mul]
          field_simp
          linarith

        -- n ↦ -1 * (-r)^(1/2n+1) is injective from ℕ to S
        have h_f_inj : Function.Injective f := by
          intro n m h_eq
          unfold f at h_eq
          apply mul_left_cancel₀ (by norm_num) at h_eq

          have rneg : (-r) > 0 := by linarith
          have r_ne: (-r) ≠ 1 := by
            intro heq
            have : r = -1 := by linarith only [heq]
            exact r_notin.1 this
          apply (rpow_right_inj rneg r_ne |>.mp) at h_eq
          field_simp at h_eq
          symm; exact h_eq

        -- therefore S is infinite
        have : S.Infinite := by
          refine Set.infinite_of_injective_forall_mem (α := ℕ) (f := f) ?_ ?_
          all_goals assumption

        contradiction

    · -- on the other hand, it is routine to verify that -1, 0, 1 are sparse
      rintro (rfl | rfl | rfl)
      all_goals simp only [Set.mem_setOf_eq]
      · -- -1 is the only value of s for r = -1
        have : {s : ℝ | ∃ n : ℕ, 0 < n ∧ s ^ n = -1} = {-1} := by
          ext s
          constructor
          · rintro ⟨n, npos, hn⟩
            simp
            exact (pow_eq_neg_one_iff.mp hn |>.1)
          · rintro rfl
            simp
            use 1
            norm_num
        rw [this]
        simp
      · -- 0 is the only value of s for r = 0
        have : {s : ℝ | ∃ n : ℕ, 0 < n ∧ s ^ n = 0} = {0} := by
          ext s
          constructor
          · intro ⟨n, npos, hn⟩
            simp
            exact pow_eq_zero hn
          · rintro rfl
            simp
            use 1
            norm_num
        rw [this]
        simp
      · -- 1 and -1 are the only values of s for r = 1
        have : {s : ℝ | ∃ n : ℕ, 0 < n ∧ s ^ n = 1} = {-1, 1} := by
          ext s
          constructor
          · rintro ⟨n, npos, hn⟩
            simp
            rcases pow_eq_one_iff_cases.mp hn with hn' | ha | ha
            · linarith only [hn', npos]
            · right; exact ha
            · left; exact ha.1
          · rintro (rfl | rfl)
            all_goals simp
            · use 2; norm_num
            · use 1; norm_num
        rw [this]
        simp
