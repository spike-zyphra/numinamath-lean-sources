import Mathlib

open Finset

theorem number_theory_195366 {x:ℤ} {s1 s2: Finset ℤ}
  (sumeq: ∑ i ∈ (Icc 0 85), (x + i) = 2021)
  (hs1: s1 = Finset.filter (x + · > (0:ℤ)) (Icc 0 85))
  (hs2: s2 = Finset.filter (x + · < (0:ℤ)) (Icc 0 85)):
  (∑ i ∈ s1, (x+i))/(s1.card:ℝ) - (∑ i ∈ s2, (x+i))/(s2.card:ℝ) = 43.5 := by

  have sum_0_to_n {n:ℕ}: ∑ i ∈ (Icc 0 n), i = n*(n+1) / 2 := by
    induction' n with n ih
    · simp
    · rw [sum_Icc_succ_top (by positivity), ih]
      have h1: 2 ∣ n*(n+1) := by
        apply even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
      have h2: 2 ∣ (n+1) * (n+1+1) := by
        apply even_iff_two_dvd.mp (Nat.even_mul_succ_self (n+1))
      zify at h1 h2
      qify
      rw [Int.cast_div h1 (by norm_num), Int.cast_div h2 (by norm_num)]
      field_simp
      ring


  have sum_x_eq: ∑ i ∈ (Icc 0 85), (x+i) = 86*x + 3655 := by
    rw [sum_add_distrib]
    have h1: ∑ i ∈ (Icc (0:ℤ) 85), x = 86 * x := by
      simp
    have h2: ∑ i ∈ Icc (0:ℤ) 85, i = 3655 := by
      have: ∑ i ∈ Icc 0 85, i = 3655 := by
        rewrite [sum_0_to_n]
        norm_num
      zify at this
      rewrite [← this]
      rfl
    rw [h1, h2]


  have xeq: x = -19 := by
    have: 86*x = - 1634 := by
      rw [sumeq] at sum_x_eq
      linarith only [sum_x_eq]
    linarith only [this]

  replace hs1: s1 = Icc 20 85 := by
    rw [hs1, xeq]
    ext i
    simp only [gt_iff_lt, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨_, ile85⟩, hi⟩
      replace hi: 1 ≤ -19+i := by exact hi
      exact ⟨(by linarith only [hi]), ile85⟩
    · rintro ⟨ige20, ile85⟩
      constructor
      · constructor <;> linarith only [ige20, ile85]
      · linarith only [ige20]

  replace hs2: s2 = Icc 0 18 := by
    rw [hs2, xeq]
    ext i
    simp only [Int.reduceNeg, neg_add_lt_iff_lt_add,
    add_zero, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨ige0, _⟩, hi⟩
      refine ⟨ige0, ?_⟩
      exact Int.lt_add_one_iff.mp hi
    · rintro ⟨ige0, ile18⟩
      constructor
      · constructor <;> linarith only [ige0, ile18]
      · linarith only [ile18]

  have Icc_eq_succ_Ico {a b:ℤ}: Icc a b = Ico a (b+1) := by
    aesop

  have pos_term_sum_aux: ∑ i ∈ Icc 20 85, (x+i) =
    ∑ i ∈ Icc 0 65, (x+20 + i) := by
    have h1: (85:ℤ) + 1 = 65+1 + 20 := by norm_num
    nth_rw 1 [← zero_add 20]
    rw [Icc_eq_succ_Ico, Icc_eq_succ_Ico, h1, ← sum_Ico_add]
    apply sum_congr rfl ?_
    intro _ _; ring

  have pos_term_sum: ∑ i ∈ s1, (x+i) = 2211 := by
    rw [hs1, pos_term_sum_aux, sum_add_distrib]
    have h1: ∑ i ∈ Icc (0:ℤ) 65, (x+20) = 66 := by
      rw [xeq]
      simp
    have h2: ∑ i ∈ Icc (0:ℤ) 65, i = 2145 := by
      have: ∑ i ∈ Icc 0 65, i = 2145 := by
        rewrite [sum_0_to_n]
        norm_num
      zify at this
      rewrite [← this]
      rfl
    rewrite [h1, h2]
    norm_num

  have neg_term_sum: ∑ i ∈ s2, (x+i) = -190 := by
    rw [hs2, sum_add_distrib]
    have h1: ∑ i ∈ Icc (0:ℤ) 18, x = - 361 := by
      rw [xeq]
      simp
    have h2: ∑ i ∈ Icc (0:ℤ) 18, i = 171 := by
      have: ∑ i ∈ Icc 0 18, i = 171 := by
        rewrite [sum_0_to_n]
        norm_num
      zify at this
      rewrite [← this]
      rfl
    rewrite [h1, h2]
    norm_num

  have pos_term_mean: (∑ i ∈ s1, (x+i))/(s1.card:ℝ) = 33.5 := by
    have: s1.card = 66 := by
      rw [hs1]
      simp
    rw [this, pos_term_sum]
    norm_num

  have neg_term_mean: (∑ i ∈ s2, (x+i))/(s2.card:ℝ) = -10 := by
    have: s2.card = 19 := by
      rw [hs2]
      simp
    rw [this, neg_term_sum]
    norm_num

  rw [pos_term_mean, neg_term_mean]
  norm_num