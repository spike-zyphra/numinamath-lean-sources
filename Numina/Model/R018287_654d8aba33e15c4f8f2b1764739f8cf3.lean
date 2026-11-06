import Mathlib

theorem algebra_246961 {a r : ℚ} (hr : r ≠ 0) (h1 : ∑ i ∈ Finset.range 100, a * r ^ i = 10)
    (h2 : ∑ i ∈ Finset.range 300, a * r ^ i = 210) :
    ∑ i ∈ Finset.range 400, a * r ^ i = 850 := by 
  have h3 : r ≠ 1 := by 
    by_contra h
    rw [h] at h1 h2
    norm_num [Finset.sum_range_succ] at h1 h2 
    all_goals 
      linarith
  have eq100 : ∑ i in Finset.range 100, a * r ^ i = a * (1 - r^100) / (1 - r) := by
    induction' 100 with n ih
    · simp
      <;> field_simp
      <;> ring
    · simp [Finset.sum_range_succ, ih]
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring_nf
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring
  have eq300 : ∑ i in Finset.range 300, a * r ^ i = a * (1 - r^300) / (1 - r) := by
    induction' 300 with n ih
    · simp
      <;> field_simp
      <;> ring
    · simp [Finset.sum_range_succ, ih]
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring_nf
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring
  have eq400 : ∑ i in Finset.range 400, a * r ^ i = a * (1 - r^400) / (1 - r) := by
    induction' 400 with n ih
    · simp
      <;> field_simp
      <;> ring
    · simp [Finset.sum_range_succ, ih]
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring_nf
      <;> field_simp [(show 1 - r ≠ 0 by 
        intro h'
        apply h3
        linarith
      )]
      <;> ring
  
  rw [eq100] at h1
  rw [eq300] at h2
  rw [eq400] at *
  have h1_mul : a * (1 - r^100) = 10 * (1 - r) := by 
    have hne : 1 - r ≠ 0 := by 
      intro h'
      apply h3
      linarith
    field_simp [hne] at h1 ⊢
    all_goals 
      linarith
  have h2_mul : a * (1 - r^300) = 210 * (1 - r) := by 
    have hne : 1 - r ≠ 0 := by 
      intro h'
      apply h3
      linarith
    field_simp [hne] at h2 ⊢
    all_goals 
      linarith
  
  have hne : 1 - r ≠ 0 := by 
      intro h'
      apply h3
      linarith
  
  have eq3 : a * (1 - r^400) / (1 - r) = 850 := by
    have h7 : a * (1 - r^400) = 850 * (1 - r) := by
      nlinarith [sq_nonneg (r^100 - 1), sq_nonneg (r^100 + 1), sq_nonneg (r^150), sq_nonneg (r^50), sq_nonneg (a), sq_nonneg (a * (1 - r ^ 100)), sq_nonneg (a * (1 - r ^ 300)), sq_nonneg (r^100 - 19), sq_nonneg (1 - r)]
    have hne' : 1 - r ≠ 0 := hne
    field_simp [hne']
    all_goals 
      linarith
  all_goals 
    linarith [eq3]