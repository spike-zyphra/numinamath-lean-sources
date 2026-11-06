import Mathlib
open Finset Set Nat Real
noncomputable section

-- Lemma to prove the sum of absolute differences equals $9$ times the absolute difference from the center.
lemma sum_abs_dist (k : ℕ) (a : ℝ) (h : a < k ∨ a > k + 8) :
    ∑ i ∈ Finset.range 9, |(k + i) - a| = 9 * |a - (k + 4)| := by
  have h_sum : ∑ i ∈ Finset.range 9, ((k : ℝ) + i) = 9 * (k + 4) := by
    rw [Finset.sum_add_distrib]
    have h_k : ∑ i ∈ Finset.range 9, (k : ℝ) = 9 * (k : ℝ) := by
      simp [Finset.sum_const]
    have h_i : ∑ i ∈ Finset.range 9, ↑i = (8 * 9 / 2 : ℝ) := by
      have h_nat_sum : ∑ i ∈ Finset.range 9, i = 8 * 9 / 2 := by
        rw [Finset.sum_range_id]
      have h_coe_sum : (∑ i ∈ Finset.range 9, (i : ℝ)) = (∑ i ∈ Finset.range 9, i : ℝ) := by
        simp [Finset.sum_congr]
      rw [h_coe_sum, ← Nat.cast_sum, h_nat_sum]
      norm_num
    rw [h_k,h_i]
    norm_num
    ring
  -- Handle cases where $a < k or a > k + 8$ separately.
  cases h with
  | inl h_left =>
    have h_dist : ∀ i ∈ Finset.range 9, ((k : ℝ) + i) - a ≥ 0 := by
      intro i hi
      simp [Finset.mem_range] at hi
      linarith
    have : ∑ i ∈ Finset.range 9, |((k : ℝ) + i) - a| = ∑ i ∈ Finset.range 9, ((k : ℝ) + i - a) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg (h_dist i hi)]
    rw [this, Finset.sum_sub_distrib, h_sum]
    have h_a_neg : a - (↑k + 4) < 0 := by linarith
    have h_abs : |a - (↑k + 4)| = (↑k + 4) - a := by
      rw [abs_of_neg h_a_neg]
      ring
    have h_sum_a : ∑ x ∈ Finset.range 9, a = 9 * a := by
      rw [Finset.sum_const, Finset.card_range]
      norm_num
    rw [h_sum_a, h_abs]
    ring_nf
  | inr h_right =>
    have h_dist : ∀ i ∈ Finset.range 9, a - ((k : ℝ) + i) ≥ 0 := by
      intro i hi
      simp [Finset.mem_range] at hi
      have h_i_bound : (i : ℝ) ≤ 8 := by exact Nat.cast_le.mpr (Nat.le_of_lt_succ hi)
      linarith
    have : ∑ i ∈ Finset.range 9, |((k : ℝ) + i) - a| = ∑ i ∈ Finset.range 9, (a - ((k : ℝ) + i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_sub_comm, abs_of_nonneg (h_dist i hi)]
    rw [this, Finset.sum_sub_distrib, h_sum]
    have h_a_pos : a - (↑k + 4) > 0 := by linarith
    have h_abs : |a - (↑k + 4)| = a - (↑k + 4) := by
      rw [abs_of_nonneg (le_of_lt h_a_pos)]
    have h_sum_a : ∑ x ∈ Finset.range 9, a = 9 * a := by
      rw [Finset.sum_const, Finset.card_range]
      norm_num
    rw [h_sum_a,h_abs]
    ring

/-6. Let's call the distance between numbers the absolute value of their difference. It is known that the sum of the distances from nine consecutive natural numbers to some number $a$ is 294, and the sum of the distances from these same nine numbers to some number $b$ is 1932. Find all possible values of $a$, given that $a+b=256$.-/
theorem algebra_152974 (a b : ℝ) (k : ℕ) (ha : ∑ i ∈ Finset.range 9, |(k + i) - a| = 294)
    (hb : ∑ i ∈ Finset.range 9, |(k + i) - b| = 1932) (hab : a + b = 256) :
    a = 13 / 3 ∨ a = 755 / 3 := by
  -- Prove $a$ is outside $[k, k+8]$.
  have h_bound : a < k ∨ a > k + 8 := by
    by_contra h_not
    push_neg at h_not
    have h_max_val : (9 : ℝ) * 8 = 72 := by norm_num
    have h_max : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - a| ≤ 9 * 8 := by
      have h_center : ∀ i ∈ Finset.range 9, |(k : ℝ) + i - a| ≤ 8 := by
        intro i hi
        simp [Finset.mem_range] at hi
        have h_lower : k ≤ a := by linarith
        have h_upper : a ≤ k + 8 := by linarith
        have h_dist : |(k : ℝ) + i - a| ≤ 8 := by
          apply abs_le.mpr
          constructor
          · calc
              (k : ℝ) + i - a ≥ k - (k + 8) := by linarith
              _ = -8 := by ring
              _ ≥ -8 := by linarith
          · calc
              (k : ℝ) + i - a ≤ (k : ℝ) + i - k := by linarith
              _ = i := by ring
              _ ≤ 8 := by
                have h_i_bound : (i : ℝ) ≤ 8 := by
                  exact Nat.cast_le.mpr (Nat.le_of_lt_succ hi)
                linarith
        exact h_dist
      have h_sum_bound : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - a| ≤ (Finset.range 9).card • (8 : ℝ) := by
        apply Finset.sum_le_card_nsmul
        intro i hi
        exact h_center i hi
      rw [Finset.card_range] at h_sum_bound
      norm_num at h_sum_bound
      rw [← h_max_val] at h_sum_bound
      exact h_sum_bound
    rw [h_max_val] at h_max
    linarith
  -- Prove $b$ is outside $[k, k+8]$.
  have h_bound_b : b < k ∨ b > k + 8 := by
    by_contra h_not
    push_neg at h_not
    have h_max_val : (9 : ℝ) * 8 = 72 := by norm_num
    have h_max : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - b| ≤ 9 * 8 := by
      have h_center : ∀ i ∈ Finset.range 9, |(k : ℝ) + i - b| ≤ 8 := by
        intro i hi
        simp [Finset.mem_range] at hi
        have h_lower : k ≤ b := by linarith
        have h_upper : b ≤ k + 8 := by linarith
        have h_dist : |(k : ℝ) + i - b| ≤ 8 := by
          apply abs_le.mpr
          constructor
          · calc
              (k : ℝ) + i - b ≥ k - (k + 8) := by linarith
              _ = -8 := by ring
              _ ≥ -8 := by linarith
          · calc
              (k : ℝ) + i - b ≤ (k : ℝ) + i - k := by linarith
              _ = i := by ring
              _ ≤ 8 := by
                have h_i_bound : (i : ℝ) ≤ 8 := by
                  exact Nat.cast_le.mpr (Nat.le_of_lt_succ hi)
                linarith
        exact h_dist
      have h_sum_bound : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - b| ≤ (Finset.range 9).card • (8 : ℝ) := by
        apply Finset.sum_le_card_nsmul
        intro i hi
        exact h_center i hi
      rw [Finset.card_range] at h_sum_bound
      norm_num at h_sum_bound
      rw [← h_max_val] at h_sum_bound
      exact h_sum_bound
    rw [h_max_val] at h_max
    linarith
  -- Apply sum_abs_dist lemma.
  have h_a : 9 * |a - (k + 4)| = 294 := by
    have h_sum_a : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - a| = ∑ i ∈ Finset.range 9, |↑k + ↑i - a| := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [← h_sum_a, sum_abs_dist k a h_bound] at ha
    exact ha
  have h_b : 9 * |b - (k + 4)| = 1932 := by
    have h_sum_b : ∑ i ∈ Finset.range 9, |(k : ℝ) + i - b| = ∑ i ∈ Finset.range 9, |↑k + ↑i - b| := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    rw [← h_sum_b, sum_abs_dist k b h_bound_b] at hb
    exact hb
  -- Simplify equations.
  have h_a_simp : |a - (k + 4)| = 294 / 9 := by
    rw [← h_a]
    field_simp
  have h_b_simp : |b - (k + 4)| = 1932 / 9 := by
    rw [← h_b]
    field_simp
  have h_a_abs : |a - (k + 4)| = 98 / 3 := by
    rw [h_a_simp]
    norm_num
  have h_b_abs : |b - (k + 4)| = 644 / 3 := by
    rw [h_b_simp]
    norm_num
  -- Solve absolute value equations.
  have h_a_cases : a - (k + 4) = 98 / 3 ∨ a - (k + 4) = -(98 / 3) := by
    exact (abs_eq (by norm_num: (0 : ℝ) ≤ 98 / 3)).mp h_a_abs
  have h_b_cases : b - (k + 4) = 644 / 3 ∨ b - (k + 4) = -(644 / 3) := by
    exact (abs_eq (by norm_num: (0 : ℝ) ≤ 644 / 3)).mp h_b_abs

  -- Analyze four cases to solve for $a$, ruling out cases where $k$ is not a natural number.
  have h_a_solutions : a = 13 / 3 ∨ a = 755 / 3 := by
    cases h_a_cases with
    | inl h_a_cases =>
      -- Analyze $b - (k + 4) = 644/3$ or $-(644/3)$ when $a - (k + 4) = 98/3$.
      cases h_b_cases with
      | inl h_b_cases =>
        have h_ab_sum := hab
        have h_ab_eq_256 : a + b = 256 := h_ab_sum
        have h_a_minus_k : a - (k + 4) = 98 / 3 := h_a_cases
        have h_b_minus_k : b - (k + 4) = 644 / 3 := h_b_cases
        have h_k_value : k = (1 : ℝ)/ 3 := by nlinarith
        -- Contradiction since $k = 1/3$ is not a natural number.
        have : False := by
          have h_lt_one : (k : ℝ) < 1 := by
            rw [h_k_value]
            norm_num
          have h_k_bound : k = 0 ∨ k ≥ 1 := by omega
          cases h_k_bound with
          | inl h_k_bound =>
            have h_k_zero : (k : ℝ) = 0 := by simp [h_k_bound]
            rw [h_k_zero] at h_k_value
            norm_num at h_k_value
          | inr h_k_bound =>
            have h_k_ge_one : (k : ℝ) ≥ 1 := by simp [h_k_bound]
            rw [h_k_value] at h_lt_one
            norm_num at h_lt_one
            linarith
        contradiction
      | inr h_b_cases =>
        have h_ab_sum := hab
        have h_ab_eq_256 : a + b = 256 := h_ab_sum
        have h_a_minus_k : a - (k + 4) = 98 / 3 := h_a_cases
        have h_b_minus_k : b - (k + 4) = -(644 / 3) := h_b_cases
        have h_a_value : a = 755 / 3 := by nlinarith
        exact Or.inr h_a_value
    | inr h_a_cases =>
      cases h_b_cases with
      | inl h_b_cases =>
        have h_ab_sum := hab
        have h_ab_eq_256 : a + b = 256 := h_ab_sum
        have h_a_minus_k : a - (k + 4) = -(98 / 3) := h_a_cases
        have h_b_minus_k : b - (k + 4) = 644 / 3 := h_b_cases
        have h_a_value : a = 13 / 3 := by nlinarith
        exact Or.inl h_a_value
      | inr h_b_cases =>
        have h_ab_sum := hab
        have h_ab_eq_256 : a + b = 256 := h_ab_sum
        have h_a_minus_k : a - (k + 4) = -(98 / 3) := h_a_cases
        have h_b_minus_k : b - (k + 4) = -(644 / 3) := h_b_cases
        have h_k_value : k = (743 : ℝ)/ 3 := by nlinarith
        -- Contradiction since $k = 743/3$ is not a natural number.
        have : False := by
          have h_lt_one : (k : ℝ) ≤ 248 := by
            rw [h_k_value]
            norm_num
          have h_k_le_248 : k ≤ 248 := by
            exact Nat.cast_le.mp h_lt_one
          have h_k_bound : k ≤ 247 ∨ k = 248 := Nat.of_le_succ h_k_le_248
          cases h_k_bound with
          | inr h_k_bound =>
            have h_k_zero : (k : ℝ) = 248 := by simp [h_k_bound]
            rw [h_k_zero] at h_k_value
            norm_num at h_k_value
          | inl h_k_bound =>
            have h_k_ge_one : (k : ℝ) ≤ 247 := by simp [h_k_bound]
            rw [h_k_value] at h_lt_one
            norm_num at h_lt_one
            linarith
        contradiction
  exact h_a_solutions
