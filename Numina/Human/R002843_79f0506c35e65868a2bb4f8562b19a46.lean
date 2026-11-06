import Mathlib

open Nat

/-- `2 ^ n ≤ n ^ 2` implies `n ≤ 4`. -/
lemma lemma_1 {n : ℕ} (hn : 2 ^ n ≤ n ^ 2) : n ≤ 4 := by
  by_contra! bn : 5 ≤ n
  induction n, bn using Nat.le_induction with
  | base => norm_num at hn
  | succ m hm ih =>
    have ineq : (m + 1) ^ 2 ≤ 2 * m ^ 2 := by
      rw [add_sq, two_mul, two_mul, mul_one, one_pow, add_assoc]; gcongr
      calc
        _ ≤ 3 * m := by ring_nf; omega
        _ ≤ _ := by rw [sq]; gcongr; omega
    replace ineq := hn.trans ineq
    rw [pow_succ'] at ineq
    exact ih (Nat.le_of_mul_le_mul_left ineq zero_lt_two)

/-- `3 ^ n ≤ n ^ 3` implies `n ≤ 3`. -/
lemma lemma_2 {n : ℕ} (hn : 3 ^ n ≤ n ^ 3) : n ≤ 3 := by
  by_contra! bn : 4 ≤ n
  induction n, bn using Nat.le_induction with
  | base => norm_num at hn
  | succ m hm ih =>
    have ineq : (m + 1) ^ 3 ≤ 3 * m ^ 3 :=
      calc
        _ = 1 * 1 + m * 3 + m * m * 3 + m ^ 3 := by ring
        _ ≤ m * m + m * m + m * m * 3 + m ^ 3 := by gcongr <;> omega
        _ = (5 + m) * m ^ 2 := by ring
        _ ≤ (3 * m) * m ^ 2 := by gcongr; linarith only [hm]
        _ = _ := by ring
    replace ineq := hn.trans ineq
    rw [Nat.pow_succ'] at ineq
    exact ih (Nat.le_of_mul_le_mul_left ineq zero_lt_three)

/-- Find all natural numbers $a,b,c$ satisfying the condition $a^b + b^c = abc$. -/
theorem number_theory_120853 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ b + b ^ c = a * b * c ↔ (a, b, c) ∈ ({(1, 1, 2), (2, 2, 2), (2, 2, 3), (4, 2, 3), (4, 2, 4)} : Finset (ℕ × ℕ × ℕ)) := by
  symm; constructor <;> intro h
  · -- Just check each solution
    fin_cases h <;> norm_num
  have lt1 : a ^ b < a * b * c := by
    rw [← h]; exact Nat.lt_add_of_pos_right (by positivity)
  have lt2 : b ^ c < a * b * c := by
    rw [← h]; exact Nat.lt_add_of_pos_left (by positivity)
  by_cases a_greatest : b ≤ a ∧ c ≤ a
  · -- Suppose `a` is greatest, then `a > 1` and `b < 3`
    obtain ⟨b_le_a, c_le_a⟩ := a_greatest
    have b_lt_3 : a * b * c ≤ a ^ 3 := by rw [pow_succ, sq]; gcongr
    replace b_lt_3 := lt1.trans_le b_lt_3
    have one_gt_a : 1 < a := by
      by_contra! h; rw [le_antisymm h ha, one_pow, one_pow] at b_lt_3; norm_num at b_lt_3
    rw [Nat.pow_lt_pow_iff_right one_gt_a] at b_lt_3
    interval_cases b
    · -- `b` cannot be 1 because the original equation would then imply `1 ∣ a`
      simp only [pow_one, one_pow, mul_one] at h
      have := dvd_mul_right a c
      rw [← h, Nat.dvd_add_self_left, dvd_one] at this
      omega
    · -- So `b = 2` and `2 ^ c ≤ c ^ 2`, from the original equation
      have h' := h
      zify at h
      rw [← eq_sub_iff_add_eq', ← @sub_left_inj _ _ (c ^ 2 : ℤ),
        show a * 2 * c - a ^ 2 - c ^ 2 = -(a - c : ℤ) ^ 2 by ring, Int.eq_neg_comm, neg_sub] at h
      replace h := h ▸ (sq_nonneg (a - c : ℤ))
      rw [sub_nonneg] at h; norm_cast at h
      -- And hence `c ≤ 4`, yielding the solutions `(2, 2, 2), (4, 2, 3), (4, 2, 4)`
      replace h := lemma_1 h; interval_cases c
      · nlinarith only [h']
      · have : a = 2 := by nlinarith only [h']
        subst a; decide
      · have : a = 4 := by nlinarith only [h', c_le_a]
        subst a; decide
      · have : a = 4 := by nlinarith only [h']
        subst a; decide
  by_cases b_greatest : c ≤ b ∧ a ≤ b
  · -- Suppose `b` is greatest, then `b > 1` and `c < 3`
    obtain ⟨c_le_b, a_le_b⟩ := b_greatest
    have c_lt_3 : a * b * c ≤ b ^ 3 := by rw [pow_succ, sq]; gcongr
    replace c_lt_3 := lt2.trans_le c_lt_3
    have one_gt_b : 1 < b := by
      by_contra! h; rw [le_antisymm h hb, one_pow, one_pow] at c_lt_3; norm_num at c_lt_3
    rw [Nat.pow_lt_pow_iff_right one_gt_b] at c_lt_3
    interval_cases c
    · -- `c` cannot be 1 because that would imply `a = 2` from the original equation
      -- (`a ^ b = (a - 1) * b` or `a - 1 ∣ a ^ b`, but `a - 1` is coprime to `a`)...
      simp only [pow_one, one_pow, mul_one] at h
      have a_eq : a = 2 := by
        zify at h
        rw [← eq_sub_iff_add_eq, ← sub_one_mul] at h
        replace h := (sub_one_dvd_pow_sub_one (a : ℤ) b).sub ⟨_, h⟩
        rw [sub_sub_cancel_left, dvd_neg] at h
        replace h := Int.eq_one_of_dvd_one (by omega) h
        omega
      -- ...which leads to `2 ^ b = b`, contradiction
      rw [a_eq, two_mul, Nat.add_right_cancel_iff] at h
      exact absurd h Nat.lt_two_pow_self.ne'
    · -- So `c = 2` and `a ^ b ≤ a ^ 2`, from the original equation
      have h' := h
      zify at h
      rw [← eq_sub_iff_add_eq, ← @sub_left_inj _ _ (a ^ 2 : ℤ),
        show a * b * 2 - b ^ 2 - a ^ 2 = -(a - b : ℤ) ^ 2 by ring, Int.eq_neg_comm, neg_sub] at h
      replace h := h ▸ (sq_nonneg (a - b : ℤ))
      rw [sub_nonneg] at h; norm_cast at h
      change 1 ≤ a at ha
      -- and `a = 1` or `2 ≤ b`
      rcases ha.eq_or_lt with rfl | ha
      · -- `a = 1` is a contradiction
        rw [one_mul, sq, mul_lt_mul_left hb, ← not_le] at lt2
        exact absurd c_le_b lt2
      · -- `2 ≤ b` leads to the solution `(2, 2, 2)`
        rw [pow_le_pow_iff_right₀ ha] at h
        replace h := le_antisymm h c_le_b; subst h
        replace ha := le_antisymm a_le_b ha; subst ha
        decide
  -- At this point, with `a_greatest, b_greatest` being false, it must be that `a < c` and `b < c`
  rw [not_and_or, not_le, not_le] at a_greatest b_greatest
  obtain ⟨a_lt_c, b_lt_c⟩ : a < c ∧ b < c := by
    rcases a_greatest with h1 | h1
    · have := b_greatest.resolve_right (not_lt.mpr h1.le)
      exact ⟨h1.trans this, this⟩
    · refine ⟨h1, ?_⟩
      rcases b_greatest with h2 | h2
      · exact h2
      · exact h2.trans h1
  -- Similar reasoning as in the other two cases (and more power manipulation) yields `b < 3`
  have bcc3 : a * b * c ≤ c ^ 3 := by rw [pow_succ, sq]; gcongr
  replace bcc3 := lt2.trans_le bcc3
  have b_le_3 : b < 3 := by
    by_contra! h'
    have : 3 ^ c < c ^ 3 := (show 3 ^ c ≤ b ^ c by gcongr).trans_lt bcc3
    exact (not_lt.mpr (lemma_2 this.le)) (h'.trans_lt b_lt_c)
  interval_cases b
  · -- `b = 1` leads to the solution `(1, 1, 2)`
    simp only [pow_one, one_pow, mul_one] at h
    have := dvd_mul_right a c
    rw [← h, Nat.dvd_add_self_left, dvd_one] at this; subst this
    have : c = 2 := by omega
    subst this; decide
  · -- `b = 2` leads to the solution `(2, 2, 3)`
    have h' := h
    zify at h
    rw [← eq_sub_iff_add_eq', ← @sub_left_inj _ _ (c ^ 2 : ℤ),
      show a * 2 * c - a ^ 2 - c ^ 2 = -(c - a : ℤ) ^ 2 by ring, Int.eq_neg_comm, neg_sub] at h
    replace h := h ▸ (sq_nonneg _)
    rw [sub_nonneg] at h; norm_cast at h
    replace h := lemma_1 h; interval_cases c
    · have : a = 2 := by nlinarith only [h', a_lt_c]
      subst a; decide
    · nlinarith only [h', a_lt_c]
