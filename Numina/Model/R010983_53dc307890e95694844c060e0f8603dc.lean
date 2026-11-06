import Mathlib

lemma l_digits_three_digit_number {n:ℕ} (nge: n ≥ 100) (nle: n ≤ 999):
  Nat.digits 10 n = [n % 10, (n / 10 % 10), n / 100] := by
  have h1: 1 < 10 := by norm_num
  have h2: 0 < n := by linarith only [nge]
  have h3: 0 < n / 10 := by
    refine Nat.div_pos ?_ (by norm_num)
    linarith only [nge]
  have h4: 0 < n / 10 / 10 := by
    rw [Nat.div_div_eq_div_mul]
    refine Nat.div_pos ?_ (by norm_num)
    linarith only [nge]
  have h5: n / 10 / 10 / 10 = 0 := by
    simp only [Nat.div_div_eq_div_mul]
    refine Nat.div_eq_of_lt ?_
    exact Order.lt_add_one_iff.mpr nle
  rw [Nat.digits_def' h1 h2,
  Nat.digits_def' h1 h3, Nat.digits_def' h1 h4,
  h5, Nat.div_div_eq_div_mul]
  simp only [Nat.reduceMul, Nat.reduceLeDiff, Nat.digits_zero,
  List.cons.injEq, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
  Nat.reduceAdd, and_true, true_and, gt_iff_lt]
  refine Nat.div_lt_of_lt_mul ?_
  exact Order.lt_add_one_iff.mpr nle


theorem number_theory_214653:
  IsGreatest {n:ℕ | n ∈ Finset.Icc 100 999 ∧
    IsSquare (n - (Nat.digits 10 n).sum)} 919 := by 
  constructor
  · -- Show 919 is in the set
    constructor
    · -- Show 919 is in the range
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show that 919 - sum of its digits is a square
      rw [l_digits_three_digit_number (by norm_num) (by norm_num)]
      native_decide
  · -- Show that for any n in the set, n ≤ 919
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [l_digits_three_digit_number] at hn2 ⊢ 
              <;> try { 
              contrapose! hn2 
              native_decide 
              <;> contradiction 
            }