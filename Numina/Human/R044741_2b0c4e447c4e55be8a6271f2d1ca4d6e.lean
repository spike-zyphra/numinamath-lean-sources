import Mathlib

open Nat Finset BigOperators

theorem inequalities_607656 (m n : ℕ) (hm : m > 0) (hn : n > 0) :
  factorial (m + n) * m^m * n^n < (m + n)^(m + n) * factorial m * factorial n := by

  have H_bin : (m + n)^(m + n) = ∑ k in range (m + n + 1), choose (m + n) k * m^k * n^(m + n - k) := by
    rw [add_pow m n (m + n)]
    apply Finset.sum_congr rfl
    intro k _
    ac_rfl

  have h_m_le_m_add_n : m ≤ m + n := Nat.le_add_right m n
  have h_term_m_exists : m ∈ range (m + n + 1) := mem_range.mpr (lt_succ.mpr h_m_le_m_add_n)

  let term_m := choose (m + n) m * m^m * n^(m + n - m)
  have h_term_m_def : term_m = choose (m + n) m * m^m * n^n := by
    unfold term_m
    rw [add_tsub_cancel_left m n]

  have term_m_pos : term_m > 0 := by
    rw [h_term_m_def]
    apply Nat.mul_pos
    · apply Nat.mul_pos
      · exact Nat.choose_pos h_m_le_m_add_n
      · exact Nat.pow_pos hm
    · exact Nat.pow_pos hn

  let S := range (m + n + 1)
  let f := fun k => choose (m + n) k * m^k * n^(m + n - k)

  have sum_decomp : ∑ k in S, f k = f m + ∑ k in S.filter (fun k ↦ k ≠ m), f k := by
    rw [Finset.sum_eq_add_sum_diff_singleton h_term_m_exists f]
    have h_set_eq : S \ {m} = S.filter (fun k ↦ k ≠ m) := by
      rw [Finset.sdiff_eq_filter]
      apply Finset.filter_congr
      intro x _hx
      simp only [Finset.mem_singleton]
    rw [h_set_eq]

  have terms_nonneg : ∀ k ∈ S, 0 ≤ f k := by
    intro k _
    exact Nat.zero_le (f k)

  have sum_rest_pos : ∑ k in S.filter (fun k ↦ k ≠ m), f k > 0 := by
    apply sum_pos'
    · intro k hk
      simp only [mem_filter] at hk
      apply terms_nonneg k hk.1
    · use 0
      have h_zero_in_S : 0 ∈ S := mem_range.mpr (Nat.succ_pos (m + n))
      have h_m_ne_zero : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
      have h_zero_in_filter : 0 ∈ S.filter (fun k => k ≠ m) := by
        simp [mem_filter, h_zero_in_S, Ne.symm h_m_ne_zero]
      have f_zero_pos : f 0 > 0 := by
        simp only [f, choose_zero_right, pow_zero, one_mul]
        exact Nat.pow_pos hn
      exact ⟨h_zero_in_filter, f_zero_pos⟩

  have sum_gt_term_m : (m + n)^(m + n) > term_m := by
    rw [H_bin]
    rw [sum_decomp]
    have fm_eq_term_m : f m = term_m := by
      rw [h_term_m_def]
      unfold f
      simp [add_tsub_cancel_left m n]
    rw [fm_eq_term_m]
    apply Nat.lt_add_of_pos_right
    exact sum_rest_pos

  have fact_m_pos : factorial m > 0 := Nat.factorial_pos m
  have fact_n_pos : factorial n > 0 := Nat.factorial_pos n
  have fact_mn_pos : factorial m * factorial n > 0 := Nat.mul_pos fact_m_pos fact_n_pos

  have step1 : (m + n)^(m + n) * (factorial m * factorial n) > term_m * (factorial m * factorial n) :=
     Nat.mul_lt_mul_of_pos_right sum_gt_term_m fact_mn_pos

  have choose_identity : choose (m + n) m * factorial m * factorial n = factorial (m + n) := by
    have h_le := Nat.le_add_right m n
    have := Nat.choose_mul_factorial_mul_factorial h_le
    rw [add_tsub_cancel_left m n] at this
    exact this

  have right_side_simplify : term_m * (factorial m * factorial n) = factorial (m + n) * m^m * n^n := by
      rw [h_term_m_def]
      rw [←choose_identity]
      ac_rfl

  rw [right_side_simplify] at step1

  apply GT.gt.lt at step1
  nth_rewrite 2 [mul_assoc]
  exact step1
