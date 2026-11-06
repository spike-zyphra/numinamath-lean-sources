import Mathlib

open Real

/- To find the tangents of the angles in a triangle,
if they are integers.-/

theorem number_theory_253115 (a b c : ℝ) (h0: a + b + c = π) (h1: 0 < a) (h2 : a ≤ b)
    (h3: b ≤ c) (h4: c ≠ π / 2) (ha: ∃ p: ℤ, tan a = p) (hb: ∃ q: ℤ, tan b = q) (hc: ∃ r: ℤ, tan c = r):
    tan a = 1 ∧ tan b = 2 ∧ tan c = 3 := by

    obtain ⟨p, ha⟩ := ha
    obtain ⟨q, hb⟩ := hb
    obtain ⟨r, hc⟩ := hc
    have la: a ≤ π / 3 := by
      linarith
    have lb: b < π / 2 := by
      linarith

    -- we first show that tan a = 1
    have f1: tan a = 1 := by
      suffices l: tan a ≤ √3 by
        replace l: tan a < 2 := by
          suffices √3 < 2 by linarith
          rw [Real.sqrt_lt']
          norm_num
          norm_num
        rw [ha] at l
        simp [ha]
        norm_cast at l
        have i: 0 < p := by
          rify
          rw [← ha]
          apply Real.tan_pos_of_pos_of_lt_pi_div_two
          linarith
          linarith
        clear *- i l
        omega
      rw [← Real.tan_pi_div_three]
      by_cases l: a = π / 3
      .
        rw [l]
      .
        replace la: a < π / 3 := by
          by_contra! r
          replace r: a = π / 3 := by
            linarith
          tauto
        suffices tan a < tan (π / 3) by linarith
        apply Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
        .
          linarith
        .
          linarith
        tauto

    -- then we can show the rest
    refine ⟨f1, ?_⟩
    rw [show a = π - (b + c) by linarith] at f1
    rw [Real.tan_pi_sub] at f1
    rw [Real.tan_add'] at f1
    have l1: 0 < q := by
      rify
      rw [← hb]
      apply Real.tan_pos_of_pos_of_lt_pi_div_two
      linarith
      linarith

    -- show that the denominator is nonzero to use field simp
    have o: 1 - tan b * tan c ≠ 0 := by
      by_contra! o
      simp [hb, hc] at o
      rify at l1
      have l2: 0 < r := by
        clear *- l1 o
        rify
        nlinarith
      replace o: q * r = 1 := by
        rify
        clear *- o
        linarith
      simp at l1
      have i: q = 1 := by
        clear *- l1 l2 o
        suffices q ≤ 1 by omega
        nlinarith
      simp [i] at o
      simp [i, o] at hb hc
      simp [hb, hc] at f1
    field_simp at f1
    simp [hb, hc] at f1
    replace f1: (q - 1) * (r - 1) = 2 := by
      rify
      clear *- f1
      nlinarith
    simp [hb, hc]
    have lc: c < π / 2 := by
      by_contra! i
      have j: tan c < 0 := by
        rw [show c = π - (π - c) by ring]
        rw [Real.tan_pi_sub]
        suffices 0 < tan (π - c) by linarith
        apply Real.tan_pos_of_pos_of_lt_pi_div_two
        .
          linarith
        .
          by_contra! g
          replace g: c = π / 2 := by linarith
          tauto
      simp [hc] at j
      clear *- j l1 f1
      have i: 2 ≤ 0 := by
        zify
        rw [← f1]
        clear f1
        nlinarith
      norm_num at i

    -- show that q ≤ r
    have l: q ≤ r := by
      by_cases s: q = r
      .
        simp [s]
      .
        rify
        simp [← hb, ← hc]
        suffices tan b < tan c by linarith [this]
        apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
        .
          linarith
        .
          tauto
        .
          suffices b ≠ c by
            by_contra! o
            replace o: b = c := by linarith
            tauto
          by_contra! g
          simp [g] at hb
          rw [hc] at hb
          simp at hb
          tauto

    -- finally, derive the tangent of b and c
    clear *- f1 l1 l
    norm_cast
    have lq: q < 3 := by nlinarith
    have u: q ≠ 1 := by
      by_contra! u
      simp [u] at f1
    have v: q = 2 := by omega
    simp [v] at f1
    omega
    .
      refine ⟨?_, ?_⟩
      .
        intro k
        by_contra! o
        have l1: -1 < k := by
          rify
          nlinarith
        have l2: k < 1 := by
          rify
          nlinarith
        have j: k = 0 := by
          clear *- l1 l2
          omega
        simp [j] at o
        clear *- o h0 h1 h2 h3
        nlinarith
      .
        intro k
        by_contra! o
        have l1: -1 < k := by
          rify
          nlinarith
        have l2: k < 1 := by
          rify
          nlinarith
        have j: k = 0 := by
          clear *- l1 l2
          omega
        simp [j] at o
        clear *- o h0 h1 h2 h3 h4
        tauto