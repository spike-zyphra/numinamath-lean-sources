import Mathlib

/-The product of five different integers is 12 . What is the largest of the integers?-/

theorem number_theory_237075 {a b c d e: ℤ} (l1: a < b) (l2: b < c) (l3: c < d) (l4: d < e)
  (h: a * b * c * d * e = 12) : e = 3 := by

  -- we first show that a < 0
  have ha: a < 0 := by
    by_contra! l
    have h1: 1 ≤ a := by
      by_contra! s
      replace l: a = 0 := by omega
      simp [l] at h
    have h2: 2 ≤ b := by omega
    have h3: 3 ≤ c := by omega
    have h4: 4 ≤ d := by omega
    have h5: 5 ≤ e := by omega
    have s1: 2 ≤ a * b := by nlinarith
    have s2: 6 ≤ a * b * c := by nlinarith
    have s3: 24 ≤ a * b * c * d := by nlinarith
    have s4: 120 ≤ a * b * c * d * e := by nlinarith
    simp [h] at s4

  -- then we show that b < 0 
  have hb: b < 0 := by
    by_contra! s
    replace s: 0 < b := by
      by_contra! t
      replace s: b = 0 := by omega
      simp [s] at h
    have h1: a * b < 0 := by nlinarith
    have h2: a * b * c < 0 := by nlinarith
    have h3: a * b * c * d < 0 := by nlinarith
    have h4: a * b * c * d * e < 0 := by nlinarith
    simp [h] at h4
  
  -- then we show that 0 < c
  have hc: 0 < c := by
    by_contra! s
    replace s: c < 0 := by
      by_contra! r
      replace s: c = 0 := by omega
      simp [s] at h
    -- then we must have d < 0
    have hd: d < 0 := by
      by_contra! t
      have f1: 0 ≤ a * b := by nlinarith
      have f2: a * b * c ≤ 0 := by nlinarith
      have f3: a * b * c * d ≤ 0 := by nlinarith
      have f4: a * b * c * d * e ≤ 0 := by nlinarith
      simp [h] at f4
    have f1: d ≤ -1 := by omega
    have f2: c ≤ -2 := by omega
    have f3: b ≤ -3 := by omega
    have f4: a ≤ -4 := by omega
    have g1: 12 ≤ a * b := by nlinarith
    have g2: a * b * c ≤ -24 := by nlinarith
    have g3: 24 ≤ a * b * c * d := by nlinarith
    by_cases le: 0 < e
    .
      have g4: 24 ≤ a * b * c * d * e := by nlinarith
      simp [h] at g4
    .
      have g4: a * b * c * d * e ≤ -24 := by nlinarith
      simp [h] at g4

  -- then we can write the terms in positive intergers
  set a':= -a with ha'
  set b':= -b with hb'
  replace ha': a = - a' := by
    simp [ha']
  replace hb': b = - b' := by
    simp [hb']
  simp [ha', hb'] at *
  clear l2 ha
  clear_value a' b'
  have r1: 1 ≤ b' := by omega
  have r2: 2 ≤ a' := by omega
  have g1: 2 ≤ a' * b' := by
    nlinarith
  have r3: 1 ≤ c := by
    omega
  have r4: 2 ≤ d := by omega
  have g2: 2 ≤ a' * b' * c := by
    nlinarith
  have g3: 4 ≤ a' * b' * c * d := by
    nlinarith
  have g4: e ≤ 3 := by nlinarith
  have g5: 2 < e := by omega
  omega