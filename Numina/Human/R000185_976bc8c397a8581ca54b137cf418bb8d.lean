import Mathlib

open BigOperators Real Nat Topology Rat

set_option maxHeartbeats 0

/- A natural number is a factorion is it is the sum of the factorials os each of its decimal digits. For example, $145$ is a factorion because $145 = 1! + 4! + 5!$. Find every 3-digit number which is a factorion. -/

theorem number_theory_629 :
  {n : ℕ | ∃ (a b c : ℕ), n = 100 * a + 10 * b + c ∧ a ≥ 1 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ n = Nat.factorial a + Nat.factorial b + Nat.factorial c} = {145} := by 
  have six : Nat.factorial 6 = 720 := by 
    unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have five : Nat.factorial 5 = 120 := by 
    unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have four : Nat.factorial 4 = 24 := by 
    unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial 
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have three : Nat.factorial 3 = 6 := by 
    unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have two : Nat.factorial 2 = 2 := by 
    unfold Nat.factorial Nat.factorial Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have one : Nat.factorial 1 = 1 := by 
    unfold Nat.factorial Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  have zero : Nat.factorial 0 = 1 := by 
    unfold Nat.factorial
    simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul]
  refine Eq.symm (Set.ext ?h); simp only [Set.mem_singleton_iff, ge_iff_le, Set.mem_setOf_eq]
  intro x; constructor
  intro h; use 1, 4, 5
  simp only [mul_one, reduceMul, reduceAdd, le_refl, one_le_ofNat, reduceLeDiff,
    factorial_one, true_and]
  rw [five, four]; norm_num; exact h
  rintro ⟨a, b, c, ⟨eq, h₁, h₂, h₃, h₄, h⟩⟩ 
  rw [eq] at h
  have A : a ≤ 6 := by
    by_contra p; have : a ≥ 7 := by linarith
    have : Nat.factorial a ≥ 7! := factorial_le this
    have : Nat.factorial 7 > 1000 := by 
      unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial
      simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul, gt_iff_lt, reduceLT]
    linarith
  have B : b ≤ 6 := by
    by_contra p; have : b ≥ 7 := by linarith
    have : Nat.factorial b ≥ 7! := factorial_le this
    have : Nat.factorial 7 > 1000 := by 
      unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial
      simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul, gt_iff_lt, reduceLT]
    linarith
  have C : c ≤ 6 := by
    by_contra p; have : c ≥ 7 := by linarith
    have : Nat.factorial c ≥ 7! := factorial_le this
    have : Nat.factorial 7 > 1000 := by 
      unfold Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial Nat.factorial
      simp only [succ_eq_add_one, reduceAdd, zero_add, mul_one, reduceMul, gt_iff_lt, reduceLT]
    linarith
  by_cases hyp : a = 6 
  have : Nat.factorial a + Nat.factorial b + Nat.factorial c ≥ 720 := by 
    rw [hyp]; linarith
  linarith
  have ae : a ≤ 5 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne A hyp
  by_cases hyp : a = 5 
  rw [hyp, five] at h; simp only [reduceMul] at h
  have be: b ≤ 5 := by
    by_contra l
    have : b = 6 := by linarith
    have : Nat.factorial b = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have : Nat.factorial b ≤ Nat.factorial 5 := factorial_le be
  have : Nat.factorial c ≤ Nat.factorial 5 := factorial_le ce
  linarith
  have : a ≤ 4 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne ae hyp
  by_cases hyp : a = 4
  rw [hyp, four] at h; simp only [reduceMul] at h
  have be: b ≤ 5 := by
    by_contra l
    have : b = 6 := by linarith
    have : Nat.factorial b = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  by_cases hyp' : b = 5
  rw [hyp', five] at h; simp only [reduceMul, reduceAdd] at h
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  by_cases hyp'' : c = 5
  rw [hyp'' , five] at h; linarith
  have : c ≤ 4 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne ce hyp''
  have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
  rw [four] at this; linarith
  have : b ≤ 4 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne be hyp'
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have k: Nat.factorial c ≤ Nat.factorial 5 := factorial_le ce
  have : Nat.factorial b ≤ Nat.factorial 4 := factorial_le this
  rw [five] at k; rw [four] at this
  linarith
  have : a ≤ 3 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne this hyp
  by_cases hyp : a = 3
  rw [hyp, three] at h; simp only [reduceMul] at h
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have be: b ≤ 5 := by
    by_contra l
    have : b = 6 := by linarith
    have : Nat.factorial b = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have k: Nat.factorial c ≤ Nat.factorial 5 := factorial_le ce
  have : Nat.factorial b ≤ Nat.factorial 5 := factorial_le be
  rw [five] at k this
  linarith
  have : a ≤ 2 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne this hyp
  by_cases hyp : a = 2 
  rw [hyp, two] at h; simp only [reduceMul] at h
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have be: b ≤ 5 := by
    by_contra l
    have : b = 6 := by linarith
    have : Nat.factorial b = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  by_cases hyp' : b = 5
  rw [hyp', five] at h; simp only [reduceMul, reduceAdd] at h
  have : Nat.factorial c ≤ Nat.factorial 5 := factorial_le ce
  linarith
  have : b ≤ 4 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne be hyp'
  have k: Nat.factorial b ≤ Nat.factorial 4 := factorial_le this
  have : Nat.factorial c ≤ Nat.factorial 5 := factorial_le ce
  linarith
  have : a ≤ 1 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne this hyp
  have a_sol : a = 1 := by linarith
  rw [a_sol, one] at h; simp only [reduceMul, reduceAdd] at h
  have ce: c ≤ 5 := by
    by_contra l
    have : c = 6 := by linarith
    have : Nat.factorial c = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  have be: b ≤ 5 := by
    by_contra l
    have : b = 6 := by linarith
    have : Nat.factorial b = 720 := by rw [this]; exact six
    rw [this] at h; linarith
  by_cases hyp' : b = 5
  rw [hyp', five] at h; simp only [reduceMul, reduceAdd] at h
  have ce: c ≤ 4 := by
    by_contra l
    have : c = 5 := by linarith
    have : Nat.factorial c = 120 := by rw [this]; exact five
    rw [this] at h; linarith
  have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le ce
  linarith
  have : b ≤ 4 := by 
    refine le_of_lt_succ ?_
    exact Nat.lt_of_le_of_ne be hyp'
  have b_sol : b = 4 := by
    by_contra p 
    have : b ≤ 3 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne this p
    by_cases j : b = 3
    rw [j, three] at h; simp only [reduceMul, reduceAdd] at h
    by_cases cf : c = 5 
    rw [cf, five] at h; contradiction
    have : c ≤ 4 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne ce cf
    have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
    rw [four] at this; linarith
    have : b ≤ 2 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne this j
    by_cases j : b = 2
    rw [j, two] at h; simp only [reduceMul, reduceAdd] at h
    by_cases cf : c = 5 
    rw [cf, five] at h; contradiction
    have : c ≤ 4 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne ce cf
    have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
    rw [four] at this; linarith
    have : b ≤ 1 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne this j
    by_cases j : b = 1
    rw [j, one] at h; simp only [reduceMul, reduceAdd] at h
    by_cases cf : c = 5 
    rw [cf, five] at h; contradiction
    have : c ≤ 4 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne ce cf
    have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
    rw [four] at this; linarith
    have : b ≤ 0 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne this j
    have : b = 0 := by linarith
    rw [this, zero] at h; simp only [reduceMul, reduceAdd] at h 
    by_cases cf : c = 5 
    rw [cf, five] at h; contradiction
    have : c ≤ 4 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne ce cf
    have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
    rw [four] at this; linarith
  rw [b_sol, four] at h; simp only [reduceMul, reduceAdd] at h
  have c_sol : c = 5 := by
    by_contra l
    have : c ≤ 4 := by 
      refine le_of_lt_succ ?_
      exact Nat.lt_of_le_of_ne ce l
    have : Nat.factorial c ≤ Nat.factorial 4 := factorial_le this
    linarith
  rw [a_sol, b_sol, c_sol] at eq; linarith

