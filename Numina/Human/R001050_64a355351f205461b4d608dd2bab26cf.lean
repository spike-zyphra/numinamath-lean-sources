import Mathlib

/- What is the ratio of the sum of the odd integers between 0 and 100, to the sum of the odd integers between 100 and 200? Express your answer as a common fraction. -/
theorem algebra_20175 :
    ((∑ i in Finset.Icc 0 100, if Odd i then i else 0 : ℕ) : ℝ) / (∑ i in Finset.Icc 100 200, if Odd i then i else 0 : ℕ) = 1 / 3 := by
  -- for all $n$, $1 + 3 +\cdots + (2n - 1) = n ^ 2$
  have eqsum n : (∑ i in Finset.Icc 0 (2 * n), if Odd i then i else 0) = n ^ 2 := by
    induction' n with n hn
    norm_num
    have eqn : 2 * (n + 1) = 2 * n + 1 + 1 := by  
      ring
    rw [eqn, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
    have evenn : ¬Odd (2 * n + 1 + 1) := by
      refine Nat.not_odd_iff.mpr ?_
      refine Nat.dvd_iff_mod_eq_zero.mp ?_
      use n + 1
      ring
    norm_num [hn, evenn]
    ring
    any_goals
    linarith
  -- so $1 + 3 +\cdots + 99 = 50 ^ 2$ and $1 + 3 +\cdots + 199 = 100 ^ 2$
  have eqicc100 := eqsum 50
  have eqicc200 := eqsum 100
  -- $1 + 3 +\cdots + 199 = (1 + 3 +\cdots + 99) + (101 + 103 +\cdots + 199)$
  have eq1 : (∑ i ∈ Finset.Icc 0 (2 * 100), if Odd i then i else 0) = (∑ i in Finset.Icc 0 100, if Odd i then i else 0) + ∑ i in Finset.Icc 101 200, if Odd i then i else 0 := by
    have le : 101 ≤ 201 := by
      norm_num
    have eq1 := Finset.sum_range_add_sum_Ico (fun i => if Odd i then i else 0) le
    have eq2 : (∑ k ∈ Finset.range 101, (fun i => if Odd i then i else 0) k) = ∑ k ∈ Finset.Icc 0 100, (fun i => if Odd i then i else 0) k := by
      rw [← Finset.sum_Ico_add_eq_sum_Icc, Nat.Ico_zero_eq_range, Finset.sum_range_succ]
      norm_num
    have eq3 : (∑ k ∈ Finset.range 201, (fun i => if Odd i then i else 0) k) = ∑ k ∈ Finset.Icc 0 200, (fun i => if Odd i then i else 0) k := by
      rw [← Finset.sum_Ico_add_eq_sum_Icc, Nat.Ico_zero_eq_range, Finset.sum_range_succ]
      norm_num
    rw [eq2, eq3] at eq1
    rw [← eq1]
    have eq4 : Finset.Ico 101 201 = Finset.Icc 101 200 := by
      rw [Nat.Ico_succ_right]
    rw [eq4]
  -- the sum of odds between 101 and 200 is equal to the sum of odds between 100 and 200
  have eq2 : (∑ i in Finset.Icc 101 200, if Odd i then i else 0) = ∑ i in Finset.Icc 100 200, if Odd i then i else 0 := by
    nth_rw 2 [← Finset.add_sum_Ioc_eq_sum_Icc]
    have mid : ¬Odd 100 := by
      exact Nat.not_odd_iff.mpr rfl
    have mid2 : Finset.Icc 101 200 = Finset.Ioc 100 200 := by
      exact rfl
    norm_num [mid, mid2]
    norm_num
  -- so $101 + 103 +\cdots + 199 = 100 ^ 2 - 50 ^ 2$
  rw [eqicc200, eqicc100, eq2] at eq1
  apply Nat.sub_eq_of_eq_add' at eq1
  -- so the result is $1 / 3$
  rw [eqicc100, ← eq1]
  norm_num