import Mathlib

/- A 150×324×375 rectangular solid is made by gluing together 1×1×1 cubes. 
An internal diagonal of this solid passes through the interiors of how many of the 
1×1×1  cubes? -/

theorem number_theory_96611
(F1: ℕ → ℚ≥0 × ℚ≥0 × NNRat)
(hF1: ∀ (k:ℕ), F1 k = (NNRat.divNat k 1, NNRat.divNat (234*k) 150,
                                       NNRat.divNat (375*k) 150))
(hs1: s1 = (Finset.image F1  (Finset.range 150)))

(F2: ℕ → NNRat × NNRat × NNRat)
(hF2: ∀ (k:ℕ), F2 k = (NNRat.divNat (150*k) 234, NNRat.divNat k 1,
                                       NNRat.divNat (375*k) 234))
(hs2: s2 = (Finset.image F2 (Finset.range 234)))

(F3: ℕ → NNRat × NNRat × NNRat)
(hF3: ∀ (k:ℕ), F3 k = (NNRat.divNat (150*k) 375, NNRat.divNat (234*k) 375,
                                       NNRat.divNat k 1))
(hs3: s3 = (Finset.image F3 (Finset.range 375)))

(F12: ℕ → NNRat × NNRat × NNRat)
(hF12: ∀ (k:ℕ), F12 k = (NNRat.divNat (25*k) 1, NNRat.divNat (39*k) 1,
                                       NNRat.divNat (125*k) 2))

(F13: ℕ → NNRat × NNRat × NNRat)
(hF13: ∀ (k:ℕ), F13 k = (NNRat.divNat (2*k) 1, NNRat.divNat (78*k) 25,
                                       NNRat.divNat (5*k) 1))

(F23: ℕ → NNRat × NNRat × NNRat)
(hF23: ∀ (k:ℕ), F23 k = (NNRat.divNat (50*k) 1, NNRat.divNat (78*k) 1,
                                       NNRat.divNat (125*k) 1))

(F123: ℕ → NNRat × NNRat × NNRat)
(hF123: ∀ (k:ℕ), F123 k = (NNRat.divNat (50*k) 1, NNRat.divNat (78*k) 1,
                                       NNRat.divNat (125*k) 1))
: (s1 ∪ s2 ∪ s3).card = 150 + 234 + 375 - 6 - 3 - 75 + 3:= by
-- Injection Proofs
have F1_inj: Function.Injective F1 := by
  intros a b hfab
  rw [hF1, hF1] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h1
  simp [Rat.den_eq_one_iff] at h1
  assumption
have F2_inj: Function.Injective F2 := by
  intros a b hfab
  rw [hF2, hF2] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h2
  simp [Rat.den_eq_one_iff] at h2
  assumption
have F3_inj: Function.Injective F3 := by
  intros a b hfab
  rw [hF3, hF3] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h3
  simp [Rat.den_eq_one_iff] at h3
  assumption
have F12_inj: Function.Injective F12 := by
  intros a b hfab
  rw [hF12, hF12] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h1
  simp [Rat.den_eq_one_iff] at h1
  assumption
have F13_inj: Function.Injective F13 := by
  intros a b hfab
  rw [hF13, hF13] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h1
  simp [Rat.den_eq_one_iff] at h1
  assumption
have F23_inj: Function.Injective F23 := by
  intros a b hfab
  rw [hF23, hF23] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h1
  simp [Rat.den_eq_one_iff] at h1
  assumption
have F123_inj: Function.Injective F123 := by
  intros a b hfab
  rw [hF123, hF123] at hfab
  injection hfab with h1 h2'
  injection h2' with h2 h3
  qify at h1
  simp [Rat.den_eq_one_iff] at h1
  assumption

-- Intersection Proofs
have s1s2s3 : (s1 ∩ s2 ∩ s3) = (Finset.image F123 (Finset.range 3)) := by
  ext ⟨p1, p2, p3⟩
  apply Iff.intro
  · intro Pin
    rw [Finset.mem_inter, Finset.mem_inter] at Pin
    rcases Pin with ⟨⟨ Pin1, Pin2⟩ , Pin3⟩
    simp only [Finset.mem_image, Finset.mem_range, hs1] at Pin1
    simp only [Finset.mem_image, Finset.mem_range, hs2] at Pin2
    simp only [Finset.mem_image, Finset.mem_range, hs3] at Pin3
    rcases Pin1 with ⟨ k, hk, hF1k⟩
    rcases Pin2 with ⟨ q, hq, hF2q⟩
    rcases Pin3 with ⟨ r, hr, hF3r⟩
    -- p1 components
    have hp1: NNRat.divNat k 1 = p1 := by
      rw [hF1] at hF1k
      simp only [Prod.mk.injEq] at hF1k
      exact hF1k.1
    -- p2 components
    have hp2: NNRat.divNat q 1 = p2 := by
      simp_all only [Prod.mk.injEq]
    have hp2': NNRat.divNat (234*k) 150 = p2 := by
      simp_all only [Prod.mk.injEq]
    -- p3 components
    have hp3: NNRat.divNat r 1 = p3 := by
      simp_all only [Prod.mk.injEq]
    have hp3': NNRat.divNat (375*k) 150 = p3 := by
      simp_all only [Prod.mk.injEq]
    -- Set GCD a b c = 3
    set g := 3
    -- relationships between function arguments k,q,r and p1,p2,p3
    have hkp1: k = p1 := by
      qify at hp1
      rw [Rat.divInt_one] at hp1
      norm_num at hp1
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    have hkp2: q = p2 := by
      qify at hp2
      rw [Rat.divInt_one] at hp2
      norm_num at hp2
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    have hkp3: r = p3 := by
      qify at hp3
      rw [Rat.divInt_one] at hp3
      norm_num at hp3
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    -- set the divisibility constraints
    have hkq: 39*k = 25*q := by
      qify at hkp1 hkp2
      qify
      rw [hkp1, hkp2 , ← hp1, ← hp2']
      field_simp
      ring
    have hkr: 5*k = 2*r := by
      qify at hkp1 hkp3
      qify
      rw [hkp1, hkp3 , ← hp1, ← hp3']
      field_simp
      ring
    -- set divisibility constraint of k
    obtain ⟨k₀, hk₀⟩: 50 ∣ k := by
      have div1: 25 ∣ k := by
        have hcop: Nat.Coprime  25 39:= by norm_num
        rw [← Nat.Coprime.dvd_mul_left hcop]
        rw [hkq]
        simp only [dvd_mul_right]
      have div2: 2 ∣ k := by
        have hcop: Nat.Coprime 2 5:= by norm_num
        rw [← Nat.Coprime.dvd_mul_left hcop]
        rw [hkr]
        simp only [dvd_mul_right]
      have hcop: Nat.Coprime 2 25 := by norm_num
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop div2 div1
    simp only [Finset.mem_image, Finset.mem_range, hF123]
    use k₀
    apply And.intro
    · rw [← @Nat.mul_lt_mul_left 50 k₀ 3, ← hk₀]
      assumption
      linarith
    · simp only [Prod.mk.injEq, g]
      apply And.intro
      · rw [← hkp1, hk₀]
        simp_all only [Nat.cast_mul, Nat.cast_ofNat]
      · apply And.intro
        · rw [← hkp2]
          suffices 25*NNRat.divNat (78 * k₀) 1 = ↑(25*q) by
            simp_all only [Nat.cast_mul, Nat.cast_ofNat,
                  mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
          rw [← hkq, hk₀]
          qify
          simp only [Rat.divInt_one, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
          ring
        · rw [← hkp3]
          suffices 2*NNRat.divNat (125 * k₀) 1 = ↑(2*r) by
            simp_all only [Nat.cast_mul, Nat.cast_ofNat,
                  mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
          rw [← hkr, hk₀]
          qify
          simp only [Rat.divInt_one, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
          ring
  -- only if side
  rw [Finset.mem_inter, Finset.mem_inter]
  simp only [Finset.mem_image, Finset.mem_range, hs1]
  rintro ⟨n, hn, hFppp⟩
  rw [hF123] at hFppp
  rcases hFppp with ⟨ hp1, hp2, hp3⟩
  apply And.intro
  apply And.intro
  · use (50*n)
    rw [hF1]
    simp only [Prod.mk.injEq]
    apply And.intro
    · linarith
    apply And.intro
    · tauto
    apply And.intro
    · ring_nf
      have h11700: 11700 = 78*150 := by ring
      rw [ ← Nat.one_mul 150 , h11700, ← Nat.mul_assoc, @NNRat.divNat_mul_right 150 _ (n*78) ]
      tauto
    · ring_nf
      have h18750: 18750 = 125*150 := by ring
      rw [ ← Nat.one_mul 150 , h18750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 150 _ (n*125) ]
      tauto
  -- Point in s3
  · simp only [Finset.mem_image, Finset.mem_range, hs2]
    use (78*n)
    rw [hF2]
    simp only [Prod.mk.injEq]
    apply And.intro
    · linarith
    apply And.intro
    · ring_nf
      have h11700: 11700 = 50*234 := by ring
      rw [ ← Nat.one_mul 234 , h11700, ← Nat.mul_assoc, @NNRat.divNat_mul_right 234 _ (n*50) ]
      tauto
    · ring_nf
      have h29250: 29250 = 125*234 := by ring
      rw [ ← Nat.one_mul 234 , h29250, ← Nat.mul_assoc, @NNRat.divNat_mul_right 234 _ (n*125) ]
      repeat tauto
  -- Point in s3
  · simp only [Finset.mem_image, Finset.mem_range, hs3]
    use (125*n)
    rw [hF3]
    simp only [Prod.mk.injEq]
    apply And.intro
    · linarith
    apply And.intro
    · ring_nf
      have h18750: 18750 = 50*375 := by ring
      rw [ ← Nat.one_mul 375 , h18750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 375 _ (n*50) ]
      tauto
    · ring_nf
      have h29250: 29250 = 78*375 := by ring
      rw [ ← Nat.one_mul 375 , h29250, ← Nat.mul_assoc, @NNRat.divNat_mul_right 375 _ (n*78) ]
      repeat tauto

have s1s2 : (s1 ∩ s2) = (Finset.image F12 (Finset.range 6)) := by
  ext ⟨p1, p2, p3⟩
  apply Iff.intro
  intro Pin
  rw [Finset.mem_inter] at Pin
  rcases Pin with ⟨Pin1, Pin2⟩
  simp only [Finset.mem_image, Finset.mem_range, hs1, hs2] at Pin1 Pin2
  rcases Pin1 with ⟨ k, hk, hkF1⟩
  rcases Pin2 with ⟨ q, hq, hqF2⟩
  -- relationships between components
  have hp1': NNRat.divNat q 1 = p2 := by
    simp_all only [Prod.mk.injEq]
  have hp2': NNRat.divNat (234*k) 150 = p2 := by
    simp_all only [Prod.mk.injEq]
  have hp1: NNRat.divNat k 1 = p1 := by
    simp_all only [Prod.mk.injEq]
  have hp3: NNRat.divNat (375*k) 150 = p3 := by
    simp_all only [Prod.mk.injEq]
  simp only [Finset.mem_image, Finset.mem_range, hF12]
  -- relationships between function arguments k,q,r and p1,p2,p3
  have hkp1: k = p1 := by
    qify at hp1
    rw [Rat.divInt_one] at hp1
    norm_num at hp1
    ext : 1
    simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
  have hkp2: q = p2 := by
    qify at hp1'
    rw [Rat.divInt_one] at hp1'
    norm_num at hp1'
    ext : 1
    simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
  -- show the divisibility constraint for k and q
  have h1: 25*q = 39*k := by
    qify at hkp1 hkp2
    qify
    rw [ hkp1,  hkp2 , ← hp1, ← hp2']
    field_simp
    ring
  set g := Nat.gcd 234 150
  have hg: g = 6 := by simp only [Nat.reduceGcd, g]
  -- Index for the reduced set
  obtain ⟨k₀, hk₀⟩: 25 ∣ k := by
      have hcop: Nat.Coprime 25 39:= by norm_num
      rw [← Nat.Coprime.dvd_mul_left hcop]
      rw [← h1]
      simp only [dvd_mul_right]
  use k₀
  apply And.intro
  · linarith
  · simp only [Prod.mk.injEq, g]
    apply And.intro
    · rw [← hp1, hk₀]
    apply And.intro
    · rw [← hp2', hk₀]
      ring_nf
      have h5850: 5850 = 39*150 := by ring
      rw [← Nat.one_mul 150, h5850, ← Nat.mul_assoc, @NNRat.divNat_mul_right 150 _ (k₀*39) ]
      tauto
    · rw [← hp3, hk₀]
      have h9375 : 9375 = 125*75 := by ring
      have h150 : 150 = 2*75 := by ring
      ring_nf
      rw [h9375, h150, ← Nat.mul_assoc, @NNRat.divNat_mul_right 75 _ (k₀*125) ]
      tauto
  -- only if side
  intro hppp
  have F12_inj: Function.Injective F12 := by
    intros a b hfab
    rw [hF12, hF12] at hfab
    injection hfab with h1 h2'
    injection h2' with h2 h3
    qify at h1
    simp [Rat.den_eq_one_iff] at h1
    assumption
  -- expand definitions of the sets
  rw [Finset.mem_inter]
  simp only [Finset.mem_image, Finset.mem_range, hs1, hs2]
  simp only [Finset.mem_image, Finset.mem_range, hs2] at hppp
  rcases hppp with ⟨ r , hr6, hrp ⟩
  rw [hF12] at hrp
  simp at hrp
  -- show inclusions
  constructor
  · use (25*r)
    apply And.intro
    · linarith
    · rw [hF1]
      simp only [Prod.mk.injEq]
      constructor
      · exact hrp.1
      · apply And.intro
        · rw [← (hrp.2.1)]
          ring_nf
          have h5850: 5850 = 39*150 := by ring
          rw [h5850]
          rw [← Nat.mul_assoc, ← Nat.one_mul 150 , @NNRat.divNat_mul_right 150 _ (r*39) ]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
        · rw [← (hrp.2.2)]
          ring_nf
          have h9375: 9375 = 125*75 := by ring
          have h150: 150 = 2*75 := by ring
          rw [h9375, h150, ← Nat.mul_assoc, @NNRat.divNat_mul_right 75 _ (r*125) ]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · use (39*r)
    apply And.intro
    · linarith
    · rw [hF2]
      simp only [Prod.mk.injEq]
      constructor
      · rw [← (hrp.1)]
        ring_nf
        have h5850: 5850 = 25*234 := by ring
        rw [h5850]
        rw [← Nat.mul_assoc, ← Nat.one_mul 234 , @NNRat.divNat_mul_right 234 _ (r*25) ]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
      · apply And.intro
        · rw [← (hrp.2.1)]
        · rw [← (hrp.2.2)]
          ring_nf
          have h14625: 14625 = 125*117 := by ring
          have h234: 234 = 2*117 := by ring
          rw [h14625, h234, ← Nat.mul_assoc, @NNRat.divNat_mul_right 117 _ (r*125) ]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

have s1s3: (s1 ∩ s3) = (Finset.image F13 (Finset.range 75)) := by
  ext ⟨p1, p2, p3⟩
  apply Iff.intro
  · intro Pin
    rw [Finset.mem_inter] at Pin
    rcases Pin with ⟨ Pin1, Pin3⟩
    simp only [Finset.mem_image, Finset.mem_range, hs1, hs3] at Pin1 Pin3
    rcases Pin1 with ⟨ k, hk, hF1k⟩
    rcases Pin3 with ⟨ r, hr, hF3r⟩
    -- p1 components
    have hp1: NNRat.divNat k 1 = p1 := by
      rw [hF1] at hF1k
      simp only [Prod.mk.injEq] at hF1k
      exact hF1k.1
    -- p2 components
    have hp2': NNRat.divNat (234*k) 150 = p2 := by
      simp_all only [Prod.mk.injEq]
    -- p3 components
    have hp3: NNRat.divNat r 1 = p3 := by
      simp_all only [Prod.mk.injEq]
    have hp3': NNRat.divNat (375*k) 150 = p3 := by
      simp_all only [Prod.mk.injEq]
    -- GCD 150 375 = 75
    set g := 75
    -- relationships between function arguments k,q,r and p1,p2,p3
    have hkp1: k = p1 := by
      qify at hp1
      rw [Rat.divInt_one] at hp1
      norm_num at hp1
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    have hkp3: r = p3 := by
      qify at hp3
      rw [Rat.divInt_one] at hp3
      norm_num at hp3
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    -- set the divisibility constraints
    have hkr: 5*k = 2*r := by
      qify at hkp1 hkp3
      qify
      rw [hkp1, hkp3 , ← hp1, ← hp3']
      field_simp
      ring
    obtain ⟨k₀, hk₀⟩: 2 ∣ k := by
        have hcop: Nat.Coprime 2 5:= by norm_num
        rw [← Nat.Coprime.dvd_mul_left hcop]
        rw [hkr]
        simp only [dvd_mul_right]
    simp only [Finset.mem_image, Finset.mem_range, hF13]
    use k₀
    apply And.intro
    · rw [hk₀] at hk
      norm_num
      linarith
    · simp only [Prod.mk.injEq]
      apply And.intro
      · rw [← hk₀]
        exact hp1
      apply And.intro
      · rw [← hp2', hk₀]
        ring_nf
        have h468: 468 = 78*6 := by ring
        have h150: 150 = 25*6 := by ring
        rw [h468, h150, ← Nat.mul_assoc, @NNRat.divNat_mul_right 6 _ (k₀*78) ]
        tauto
      · rw [← hp3', hk₀]
        ring_nf
        have h750: 750 = 5*150 := by ring
        rw [ ← Nat.one_mul 150 , h750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 150 _ (k₀*5) ]
        tauto
  --- only if
  · rw [Finset.mem_inter]
    simp only [Finset.mem_image, Finset.mem_range, hs1]
    rintro ⟨n, hn, hFppp⟩
    rw [hF13] at hFppp
    rcases hFppp with ⟨ hp1, hp2, hp3⟩
    apply And.intro
    · use (2*n)
      apply And.intro
      · linarith
      · simp only [hF1, Prod.mk.injEq]
        apply And.intro
        · simp only
        apply And.intro
        · ring_nf
          have h468: 468 = 78*6 := by ring
          have h150: 150 = 25*6 := by ring
          rw [h468, h150, ← Nat.mul_assoc, @NNRat.divNat_mul_right 6 _ (n*78) ]
          tauto
        · ring_nf
          have h750: 750 = 5*150 := by ring
          rw [ ← Nat.one_mul 150 , h750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 150 _ (n*5) ]
          tauto
    · simp only [Finset.mem_image, Finset.mem_range, hs3]
      use (5*n)
      apply And.intro
      · linarith
      · simp only [hF3, Prod.mk.injEq]
        apply And.intro
        · ring_nf
          have h750: 750 = 2*375 := by ring
          rw [ ← Nat.one_mul 375 , h750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 375 _ (n*2) ]
          tauto
        apply And.intro
        · ring_nf
          have h1170: 1170 = 78*15 := by ring
          have h375: 375 = 25*15 := by ring
          rw [h1170, h375, ← Nat.mul_assoc, @NNRat.divNat_mul_right 15 _ (n*78) ]
          tauto
        · tauto

have s2s3: (s2 ∩ s3) = (Finset.image F23 (Finset.range 3)) := by
  ext ⟨p1, p2, p3⟩
  apply Iff.intro
  · intro Pin
    rw [Finset.mem_inter] at Pin
    rcases Pin with ⟨ Pin2, Pin3⟩
    simp only [Finset.mem_image, Finset.mem_range, hs2, hs3] at Pin2 Pin3
    rcases Pin2 with ⟨ q, hk, hF2q⟩
    rcases Pin3 with ⟨ r, hr, hF3r⟩
    -- p1 components
    have hp1: NNRat.divNat (150*q) 234 = p1 := by
      rw [hF2] at hF2q
      simp only [Prod.mk.injEq] at hF2q
      exact hF2q.1
    -- p2 components
    have hp2: NNRat.divNat q 1 = p2 := by
      simp_all only [Prod.mk.injEq]
    -- p3 components
    have hp3: NNRat.divNat r 1 = p3 := by
      simp_all only [Prod.mk.injEq]
    have hp3'': NNRat.divNat (375*q) 234 = p3 := by
      simp_all only [Prod.mk.injEq]
    -- GCD 150 375 = 75
    set g := 3
    -- relationships between function arguments k,q,r and p1,p2,p3
    have hqp2: q = p2 := by
      qify at hp2
      rw [Rat.divInt_one] at hp2
      norm_num at hp2
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    have hrp3: r = p3 := by
      qify at hp3
      rw [Rat.divInt_one] at hp3
      norm_num at hp3
      ext : 1
      simp_all only [NNRat.cast_natCast, NNRat.cast_divNat, Nat.cast_mul, Nat.cast_ofNat]
    -- set the divisibility constraints
    have hkr: 125*q = 78*r := by
      qify at hqp2 hrp3
      qify
      rw [hqp2, hrp3 , ← hp2, ← hp3'']
      field_simp
      ring
    -- set divisibility constraint of k
    obtain ⟨q₀, hq₀⟩: 78 ∣ q := by
      have hcop: Nat.Coprime 78 125:= by norm_num
      rw [← Nat.Coprime.dvd_mul_left hcop]
      rw [hkr]
      simp only [dvd_mul_right]
    simp only [Finset.mem_image, Finset.mem_range, hF23]
    use q₀
    apply And.intro
    · rw [hq₀] at hk
      norm_num
      linarith
    · simp only [Prod.mk.injEq]
      apply And.intro
      · rw [← hp1, hq₀]
        ring_nf
        have h11700: 11700 = 50*234 := by ring
        rw [h11700, ← Nat.mul_assoc,← Nat.one_mul 234, @NNRat.divNat_mul_right 234 _ (q₀*50) ]
        tauto
      apply And.intro
      · rw [← hp2, hq₀]
      · rw [← hp3'', hq₀]
        ring_nf
        have h29250: 29250 = 125*234 := by ring
        rw [h29250, ← Nat.mul_assoc,← Nat.one_mul 234, @NNRat.divNat_mul_right 234 _ (q₀*125) ]
        tauto
  -- only if side
  · rw [Finset.mem_inter]
    simp only [Finset.mem_image, Finset.mem_range, hs2]
    rintro ⟨n, hn, hFppp⟩
    rw [hF23] at hFppp
    rcases hFppp with ⟨ hp1, hp2, hp3⟩
    -- show ppp ∈ s2 ∩ s3
    apply And.intro
    · use (78*n)
      apply And.intro
      · linarith
      · simp only [hF2, Prod.mk.injEq]
        apply And.intro
        · ring_nf
          have h11700: 11700 = 50*234 := by ring
          rw [h11700, ← Nat.mul_assoc,← Nat.one_mul 234, @NNRat.divNat_mul_right 234 _ (n*50) ]
          tauto
        apply And.intro
        · tauto
        · ring_nf
          have h29250: 29250 = 125*234 := by ring
          rw [h29250, ← Nat.mul_assoc,← Nat.one_mul 234, @NNRat.divNat_mul_right 234 _ (n*125) ]
          tauto
    · simp only [Finset.mem_image, Finset.mem_range, hs3]
      use (125*n)
      apply And.intro
      · linarith
      · simp only [hF3, Prod.mk.injEq]
        apply And.intro
        · ring_nf
          have h18750: 18750 = 50*375 := by ring
          rw [ ← Nat.one_mul 375 , h18750, ← Nat.mul_assoc, @NNRat.divNat_mul_right 375 _ (n*50) ]
          tauto
        apply And.intro
        · ring_nf
          have h29250: 29250 = 78*375 := by ring
          rw [← Nat.one_mul 375, h29250, ← Nat.mul_assoc, @NNRat.divNat_mul_right 375 _ (n*78) ]
          tauto
        · tauto

-- Cardinalities
have s1_card: s1.card = 150 := by
  rw [hs1,  Finset.card_image_of_injective (Finset.range 150) F1_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s2_card: s2.card = 234 := by
  rw [hs2,  Finset.card_image_of_injective (Finset.range 234) F2_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s3_card: s3.card = 375 := by
  rw [hs3,  Finset.card_image_of_injective (Finset.range 375) F3_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s1s2_card: (s1 ∩ s2).card = 6 := by
  rw [s1s2,  Finset.card_image_of_injective (Finset.range 6) F12_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s1s3_card: (s1 ∩ s3).card = 75 := by
  rw [s1s3, Finset.card_image_of_injective (Finset.range 75) F13_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s2s3_card: (s2 ∩ s3).card = 3 := by
  rw [s2s3, Finset.card_image_of_injective (Finset.range 3) F23_inj]
  simp [← Set.Nat.card_coe_set_eq]
have s1s2s3_card: (s1 ∩ s2 ∩ s3).card = 3 := by
  rw [s1s2s3, Finset.card_image_of_injective (Finset.range 3) F123_inj]
  simp [← Set.Nat.card_coe_set_eq]

-- Inclusion-Exclusion with s1 ∪ s2 ∪ s3
rw [Finset.card_union, Finset.card_union, s1_card, s2_card, s1s2_card]
rw [Finset.inter_comm, Finset.inter_union_distrib_left, Finset.card_union]
rw [Finset.inter_comm, s1s3_card, Finset.inter_comm, s2s3_card]
ring_nf
rw [Finset.inter_assoc, Finset.inter_comm, Finset.inter_assoc, Finset.inter_comm]
nth_rw 2 [Finset.inter_comm]
rw [Finset.inter_assoc, Finset.inter_assoc, Finset.inter_self, ← Finset.inter_assoc, s1s2s3_card, s3_card]
ring