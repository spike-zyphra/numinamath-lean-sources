import Mathlib

open Finset

theorem number_theory_112262 (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, n ∣ k ∧ (Nat.digits 10 k).sum = n := by
  let f : ℕ → range n := fun i => ⟨10 ^ i % n, by simp; apply Nat.mod_lt; omega⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  rw [Set.infinite_coe_iff] at hy
  let a : ℕ → ℕ := fun i => Nat.nth (fun t => t ∈ f ⁻¹' {y}) i
  have amod : ∀ i, 10 ^ a i % n = y.val := by
    intro i; simp [a, f]
    have := Nat.nth_mem_of_infinite hy i
    simp [f] at this; apply_fun fun t => t.val at this
    simp at this; exact this
  have age : ∀ i, i ≤ a i := by
    intro i; have := Nat.le_nth_count hy i
    simp at this; simp [a]; apply le_trans this
    apply Nat.nth_monotone hy; apply Nat.count_le
  have amono : StrictMono a := by
    simp [a]; exact Nat.nth_strictMono hy
  have sumdig : ∀ i, (Nat.digits 10 (∑ k ∈ range i, 10 ^ a k)).sum = i := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      by_cases h : i ≤ 0
      · simp at h; simp [h]; by_cases h' : a 0 ≤ 0
        · simp at h'; simp [h']
        rw [Nat.pow_mod]; nth_rw 6 [show 10 = 10^1 by simp]
        rw [Nat.pow_div, ← mul_one (10 ^ (a 0 - 1)), Nat.digits_base_pow_mul]
        simp; rw [zero_pow]; all_goals omega
      have : (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length ≤ a i := by
        rw [Nat.digits_len, ← Nat.lt_iff_add_one_le]
        apply Nat.log_lt_of_lt_pow
        · rw [show i = 1+(i-1) by omega, sum_range_add]; simp
        · calc
            _ ≤ ∑ x ∈ range (a i), 10 ^ x := by
              rw [← sum_image]; apply sum_le_sum_of_subset
              · simp [Finset.subset_iff, a]; intro k hk
                exact Nat.nth_strictMono hy hk
              simp; intro _ _ _ _ h
              apply amono.injective at h; exact h
            _ < _ := by
              zify; rw [← mul_lt_mul_right (show (0:ℤ)<10-1 by simp)]
              rw [geom_sum_mul]; have : 1 ≤ 10 ^ a i := by apply one_le_pow₀; simp
              linarith only [this]
        simp; rw [show i = 1+(i-1) by omega, sum_range_add]; simp
      rw [sum_range_succ, ← mul_one (10 ^ a i)]
      rw [show a i = (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length + (a i -
      (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length) by omega]
      rw [← Nat.digits_append_zeroes_append_digits]; any_goals simp
      exact ih
  use ∑ x ∈ range n, 10 ^ a x; constructor
  · rw [Nat.dvd_iff_mod_eq_zero, sum_nat_mod]
    simp [amod]
  exact sumdig n