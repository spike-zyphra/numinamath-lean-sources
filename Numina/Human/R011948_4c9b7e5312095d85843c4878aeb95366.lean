import Mathlib

theorem number_theory_325943 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
    x ^ 2 + y ^ 2 = 208 * (x - y) ↔ (x = 160 ∧ y = 32) ∨ (x = 48 ∧ y = 32) := by
  constructor
  · intro h
    -- by analysis the residue of mod 4 then we get Even x, Even y
    have even_xy : Even x ∧ Even y:= by
      by_contra hc
      simp at hc
      by_cases ho : Odd x
      unfold Odd at ho
      obtain ⟨k, hk⟩ := ho
      by_cases he : Odd y
      unfold Odd at he
      obtain ⟨l, hl⟩ := he
      rw [hk, hl] at h
      ring_nf at h
      have mod_eq : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h]
        omega
      have mod_eq' : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 2 := by 
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at he
      unfold Even at he
      obtain ⟨l, hl⟩ := he
      rw [hl, hk] at h
      ring_nf at h
      have mod_eq : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h]
        omega
      have mod_eq' : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at ho
      obtain ho' := hc ho
      unfold Even at ho
      unfold Odd at ho'
      obtain ⟨k, hk⟩ := ho
      obtain ⟨l, hl⟩ := ho'
      rw [hk, hl] at h
      ring_nf at h
      have mod_eq : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by
        rw [h]
        omega
      have mod_eq' : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
    obtain ⟨even_x, even_y⟩ := even_xy
    unfold Even at even_x even_y
    obtain ⟨a, ha⟩ := even_x
    obtain ⟨b, hb⟩ := even_y
    rw [ha, hb] at h
    have h1 : a ^ 2 + b ^ 2 = 104 * (a - b):= by linarith
    have even_ab : Even a ∧ Even b := by
      by_contra hc
      simp at hc
      by_cases ho : Odd a
      unfold Odd at ho
      obtain ⟨k, hk⟩ := ho
      by_cases he : Odd b
      unfold Odd at he
      obtain ⟨l, hl⟩ := he
      rw [hk, hl] at h1
      ring_nf at h1
      have mod_eq : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h1]
        omega
      have mod_eq' : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 2 := by 
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at he
      unfold Even at he
      obtain ⟨l, hl⟩ := he
      rw [hl, hk] at h1
      ring_nf at h1
      have mod_eq : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h1]
        omega
      have mod_eq' : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at ho
      obtain ho' := hc ho
      unfold Even at ho
      unfold Odd at ho'
      obtain ⟨k, hk⟩ := ho
      obtain ⟨l, hl⟩ := ho'
      rw [hk, hl] at h1
      ring_nf at h1
      have mod_eq : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by
        rw [h1]
        omega
      have mod_eq' : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
    obtain ⟨even_a, even_b⟩ := even_ab
    unfold Even at even_a even_b
    obtain ⟨c, hc⟩ := even_a
    obtain ⟨d, hd⟩ := even_b
    rw [hc,hd] at h1
    have h2 : c ^ 2 + d ^ 2 = 52 * (c - d):= by linarith
    have even_cd : Even c ∧ Even d := by
      by_contra hc
      simp at hc
      by_cases ho : Odd c
      unfold Odd at ho
      obtain ⟨k, hk⟩ := ho
      by_cases he : Odd d
      unfold Odd at he
      obtain ⟨l, hl⟩ := he
      rw [hk, hl] at h2
      ring_nf at h2
      have mod_eq : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h2]
        omega
      have mod_eq' : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 2 := by 
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at he
      unfold Even at he
      obtain ⟨l, hl⟩ := he
      rw [hl, hk] at h2
      ring_nf at h2
      have mod_eq : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 0 := by 
        rw [h2]
        omega
      have mod_eq' : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at ho
      obtain ho' := hc ho
      unfold Even at ho
      unfold Odd at ho'
      obtain ⟨k, hk⟩ := ho
      obtain ⟨l, hl⟩ := ho'
      rw [hk, hl] at h2
      ring_nf at h2
      have mod_eq : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by
        rw [h2]
        omega
      have mod_eq' : ( 1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 1 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
    obtain ⟨even_c, even_d⟩ := even_cd
    unfold Even at even_c even_d
    obtain ⟨s, hs⟩ := even_c
    obtain ⟨t, ht⟩ := even_d
    rw [hs,ht] at h2
    have h3 : s ^ 2 + t ^ 2 = 26 * (s - t) := by linarith
    -- now solve s^2+t^2=26(s-t)
    have h4 : (s - 13) ^ 2 + (t + 13) ^ 2 = 2 * 13 ^ 2 := by 
      linarith
    have even_st : Even s ∧ Even t := by 
      by_contra hc
      simp at hc
      by_cases ho : Odd s
      unfold Odd at ho
      obtain ⟨k, hk⟩ := ho
      by_cases he : Odd t
      unfold Odd at he
      obtain ⟨l, hl⟩ := he
      rw [hk, hl] at h3
      ring_nf at h3
      have mod_eq : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 0 := by
        rw [h3]
        omega
      have mod_eq' : (2 + k * 4 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 2 := by
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at he
      unfold Even at he
      obtain ⟨l, hl⟩ := he
      rw [hl, hk] at h3
      ring_nf at h3
      have mod_eq : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 2 := by 
        rw [h3]
        omega
      have mod_eq' : (1 + k * 4 + k ^ 2 * 4 + l ^ 2 * 4) % 4 = 1 := by 
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
      simp at ho
      obtain ho' := hc ho
      unfold Even at ho
      unfold Odd at ho'
      obtain ⟨k, hk⟩ := ho
      obtain ⟨l, hl⟩ := ho'
      rw [hk, hl] at h3
      ring_nf at h3
      have mod_eq : (1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 2 := by 
        rw [h3]
        omega
      have mod_eq' : (1 + k ^ 2 * 4 + l * 4 + l ^ 2 * 4) % 4 = 1 := by 
        omega
      rw [mod_eq] at mod_eq'
      simp at mod_eq'
    obtain ⟨even_s, even_t⟩ := even_st
    have tge : t + 13 ≥ 15 := by 
      have aux : t ≥ 2 := by 
        by_contra hneg
        simp at hneg
        have tpos : t > 0 := by 
          linarith
        interval_cases t
        norm_num at even_t
      omega
    have sle1 : (s - 13) ^ 2 = 2 * 13 ^ 2 - (t + 13) ^ 2 := by 
      linarith
    have sle2 : (s - 13) ^ 2 ≤ 2 * 13 ^ 2 - 15 ^ 2 := by 
      nlinarith
    have sle_aux : (s - 13) ^ 2 < 11 ^ 2 := by 
      linarith
    have sle3 : |s - 13| < 11 := by
      apply abs_lt_of_sq_lt_sq
      exact sle_aux
      norm_num
    let m := |s - 13|
    have odd_aux : Odd m := by 
      unfold Even at even_s
      obtain ⟨k, hk⟩ := even_s
      unfold m
      by_cases spos : s - 13 ≥ 0
      have aux : |s - 13| = s - 13 := by 
        unfold abs
        simp
        linarith
      rw [aux]
      unfold Odd
      use (k - 7) 
      rw [hk]
      ring
      have aux : |s - 13| = 13 - s:= by 
        unfold abs
        simp
        linarith
      rw [aux]
      unfold Odd
      use (6 - k)
      rw [hk]
      ring
    have mle : m ≤ 10 := by 
      unfold m
      linarith
    have mpos : m ≥  0 := by
      unfold m 
      positivity
    have meq : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 9 := by
      interval_cases m
      norm_num at odd_aux
      simp
      have Even2 : Even (2 : ℤ) := by decide
      obtain aux := Int.not_odd_iff_even.mpr Even2
      by_contra _
      exact aux odd_aux
      simp
      have Even4 : Even (4 : ℤ) := by decide
      obtain aux := Int.not_odd_iff_even.mpr Even4
      by_contra _
      exact aux odd_aux
      simp
      have Even6 : Even (6 : ℤ) := by decide
      obtain aux := Int.not_odd_iff_even.mpr Even6
      by_contra _
      exact aux odd_aux
      simp
      have Even8 : Even (8 : ℤ) := by decide
      obtain aux := Int.not_odd_iff_even.mpr Even8
      by_contra _
      exact aux odd_aux
      simp 
      have Even10 : Even (10 : ℤ) := by decide
      obtain aux := Int.not_odd_iff_even.mpr Even10
      by_contra _
      exact aux odd_aux
    have tsq : (t + 13) ^ 2 = 2 * 13 ^ 2 - (s - 13) ^ 2 := by 
      linarith
    obtain meq | meq | meq | meq| meq := meq
    have seq1 : |s - 13| = 1 := by 
      simpa
    have seq2 : (s - 13) ^ 2 = 1 := by 
      apply (sq_eq_sq_iff_abs_eq_abs (s - 13) 1).mpr
      simpa
    have twq1 : (t + 13) ^ 2 = 337 := by 
      linarith
    by_contra h'
    have ineq1 : (t + 13) ^ 2 > 18 ^ 2 := by 
      linarith
    have ineq2 : (t + 13) ^ 2 < 19 ^ 2 := by
      linarith
    have ineq3 : |t + 13| > |18| := by 
      apply sq_lt_sq.mp
      linarith
    have ineq4 : |t + 13| < |19| := by 
      apply sq_lt_sq.mp
      linarith
    simp at ineq3 ineq4
    linarith
    -- case s - 13 = 3
    have seq1 : |s - 13| = 3 := by 
      simpa
    have seq2 : (s - 13) ^ 2 = 9 := by 
      apply (sq_eq_sq_iff_abs_eq_abs (s - 13) 3).mpr
      simpa
    have twq1 : (t + 13) ^ 2 = 329 := by 
      linarith
    by_contra h'
    have ineq1 : (t + 13) ^ 2 > 18 ^ 2 := by 
      linarith
    have ineq2 : (t + 13) ^ 2 < 19 ^ 2 := by
      linarith
    have ineq3 : |t + 13| > |18| := by 
      apply sq_lt_sq.mp
      linarith
    have ineq4 : |t + 13| < |19| := by 
      apply sq_lt_sq.mp
      linarith
    simp at ineq3 ineq4
    linarith
    -- case s - 13 = 5 
    have seq1 : |s - 13| = 5 := by 
      simpa
    have seq2 : (s - 13) ^ 2 = 25 := by 
      apply (sq_eq_sq_iff_abs_eq_abs (s - 13) 5).mpr
      simpa
    have twq1 : (t + 13) ^ 2 = 313 := by 
      linarith
    by_contra h'
    have ineq1 : (t + 13) ^ 2 > 17 ^ 2 := by 
      linarith
    have ineq2 : (t + 13) ^ 2 < 18 ^ 2 := by
      linarith
    have ineq3 : |t + 13| > |17| := by 
      apply sq_lt_sq.mp
      linarith
    have ineq4 : |t + 13| < |18| := by 
      apply sq_lt_sq.mp
      linarith
    simp at ineq3 ineq4
    linarith
    -- case s - 13 = 7, this is holds, the other case all leads to contradiction
    have seq1 : |s - 13| = 7 := by 
      simpa
    have seq2 : (s - 13) ^ 2 = 49 := by 
      apply (sq_eq_sq_iff_abs_eq_abs (s - 13) 7).mpr
      simpa
    have twq1 : (t + 13) ^ 2 = 289 := by 
      linarith
    have teq1 : t + 13 = 17 ∨ t + 13 = -17 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp twq1
    obtain teq1 | teq1 := teq1
    have tseq1 : t = 4 := by
      linarith
    have tseq2 : s = 6 ∨ s = 20 := by
      by_cases spos : s - 13 ≥ 0 
      have seq2 : |s - 13| = s - 13 := by 
        unfold abs
        simp
        linarith
      right
      linarith
      simp at spos
      have seq2 : |s - 13| = 13 - s := by 
        unfold abs
        simp
        linarith
      left 
      linarith
    obtain tseq2 | tseq2 := tseq2
    right
    constructor
    linarith; linarith
    left 
    constructor
    linarith; linarith
    -- the second case (t + 13 = -7) did not holds since t is positive
    linarith
    -- case s - 13 = 9, impossible since (t + 13) ^ 2 = 257 not perfect square.
    have seq1 : |s - 13| = 9 := by 
      simpa
    have seq2 : (s - 13) ^ 2 = 81 := by 
      apply (sq_eq_sq_iff_abs_eq_abs (s - 13) 9).mpr
      simpa
    have twq1 : (t + 13) ^ 2 = 257 := by 
      linarith
    by_contra h'
    have ineq1 : (t + 13) ^ 2 > 16 ^ 2 := by 
      linarith
    have ineq2 : (t + 13) ^ 2 < 17 ^ 2 := by
      linarith
    have ineq3 : |t + 13| > |16| := by 
      apply sq_lt_sq.mp
      linarith
    have ineq4 : |t + 13| < |17| := by 
      apply sq_lt_sq.mp
      linarith
    simp at ineq3 ineq4
    linarith
     
  -- prove that when x = 160 and y = 32, it satisfies the equation.
  intro h
  obtain h | h := h
  obtain ⟨xeq, yeq⟩ := h
  rw [xeq, yeq]
  norm_num
  obtain ⟨xeq, yeq⟩ := h
  rw [xeq, yeq]
  norm_num