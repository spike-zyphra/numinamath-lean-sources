import Mathlib

open Real Finset

theorem algebra_208088 :
    IsLeast {n : ℕ | ∃ x : Fin n → ℝ, (∑ i : Fin n, sin (x i)) = 0 ∧
      (∑ i : Fin n, (i+1) * sin (x i)) = 100} 20 := by

  constructor 
  · -- Show that 20 is indeed in the set.
    use λ i => 
      if i.val < 10 then 
        -(Real.pi / 2)
      else 
        Real.pi / 2
    constructor 
    · -- Show that the first sum is zero.
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, sin_neg, sin_pi_div_two]
      <;> norm_num 
    · -- Show that the second sum is 100.
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, sin_neg, sin_pi_div_two]
      <;> norm_num 
  · -- Show that no smaller n is in the set.
    intro n hn
    rcases hn with ⟨x, hx1, hx2⟩
    by_contra h
    push_neg at h 
    have h1 : n ≤ 19 := by linarith 
    have h3 : ∑ i : Fin n, (i + 1 : ℝ) * sin (x i) = 100 := hx2
    have h4 : ∑ i : Fin n, sin (x i) = 0 := hx1 
    interval_cases n <;> 
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hx1 hx2 ⊢
      <;> norm_num [Finset.sum_range_succ] at hx1 hx2 ⊢ 
      <;> try { 
        have h7 : sin (x 0) ≤ 1 := by apply sin_le_one
        have h8 : sin (x 0) ≥ -1 := by apply neg_one_le_sin
        have h9 : sin (x 1) ≤ 1 := by apply sin_le_one
        have h10 : sin (x 1) ≥ -1 := by apply neg_one_le_sin
        have h11 : sin (x 2) ≤ 1 := by apply sin_le_one
        have h12 : sin (x 2) ≥ -1 := by apply neg_one_le_sin
        have h13 : sin (x 3) ≤ 1 := by apply sin_le_one
        have h14 : sin (x 3) ≥ -1 := by apply neg_one_le_sin
        have h15 : sin (x 4) ≤ 1 := by apply sin_le_one
        have h16 : sin (x 4) ≥ -1 := by apply neg_one_le_sin
        have h17 : sin (x 5) ≤ 1 := by apply sin_le_one
        have h18 : sin (x 5) ≥ -1 := by apply neg_one_le_sin
        have h19 : sin (x 6) ≤ 1 := by apply sin_le_one
        have h20 : sin (x 6) ≥ -1 := by apply neg_one_le_sin
        have h21 : sin (x 7) ≤ 1 := by apply sin_le_one
        have h22 : sin (x 7) ≥ -1 := by apply neg_one_le_sin
        have h23 : sin (x 8) ≤ 1 := by apply sin_le_one
        have h24 : sin (x 8) ≥ -1 := by apply neg_one_le_sin
        have h25 : sin (x 9) ≤ 1 := by apply sin_le_one
        have h26 : sin (x 9) ≥ -1 := by apply neg_one_le_sin
        have h27 : sin (x 10) ≤ 1 := by apply sin_le_one
        have h28 : sin (x 10) ≥ -1 := by apply neg_one_le_sin
        have h29 : sin (x 11) ≤ 1 := by apply sin_le_one
        have h30 : sin (x 11) ≥ -1 := by apply neg_one_le_sin
        have h31 : sin (x 12) ≤ 1 := by apply sin_le_one
        have h32 : sin (x 12) ≥ -1 := by apply neg_one_le_sin
        have h33 : sin (x 13) ≤ 1 := by apply sin_le_one
        have h34 : sin (x 13) ≥ -1 := by apply neg_one_le_sin
        have h35 : sin (x 14) ≤ 1 := by apply sin_le_one
        have h36 : sin (x 14) ≥ -1 := by apply neg_one_le_sin
        have h37 : sin (x 15) ≤ 1 := by apply sin_le_one
        have h38 : sin (x 15) ≥ -1 := by apply neg_one_le_sin
        have h39 : sin (x 16) ≤ 1 := by apply sin_le_one
        have h40 : sin (x 16) ≥ -1 := by apply neg_one_le_sin
        have h41 : sin (x 17) ≤ 1 := by apply sin_le_one
        have h42 : sin (x 17) ≥ -1 := by apply neg_one_le_sin
        have h43 : sin (x 18) ≤ 1 := by apply sin_le_one
        have h44 : sin (x 18) ≥ -1 := by apply neg_one_le_sin 
        linarith 
      }
    all_goals try { linarith }