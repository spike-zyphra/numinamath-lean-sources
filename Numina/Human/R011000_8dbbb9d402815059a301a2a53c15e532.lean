import Mathlib

set_option maxRecDepth 400000
/-If a, b, c and d are pairwise distinct positive integers that satisfy
lcm(a,b,c,d) < 1000 and a + b = c + d, compute the largest possible value of a + b-/
theorem number_theory_610552: IsGreatest {x: ℤ | ∃ a b c d: ℤ, 0 < d ∧ d < a ∧ a < b ∧ b < c ∧
lcm (lcm (lcm a b) c) d < 1000 ∧ a + b = c + d ∧ x = a + b } 581 := by
  constructor
  -- 581 is possible
  . simp
    use 249
    use 332
    use 498
    use 83
    norm_num
    decide
  -- 581 is the largest
  . intro x h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a, b, c, d, h⟩ := h
    rcases h with ⟨hd, hda, hab, hbc, h1, h2, h3⟩
    rw [h3]
    clear h3
    set l:= lcm (lcm (lcm a b) c) d with hl
    let a':= l / a
    let b':= l / b
    let c':= l / c
    let d':= l / d
    have ha': a ∣ l := by   -- show a ∣ l
      rw [hl]
      have d1: a ∣ lcm (lcm a b) c := by
        have d2: a ∣ lcm a b := by
          apply dvd_lcm_left
        have d3: lcm a b ∣ lcm (lcm a b) c := by
          apply dvd_lcm_left
        apply dvd_trans d2 d3
      have d4: lcm (lcm a b) c ∣ lcm (lcm (lcm a b) c) d := by
        apply dvd_lcm_left
      apply dvd_trans d1 d4
    have hb': b ∣ l := by  -- show b ∣ l
      rw [hl]
      have d1: b ∣ lcm (lcm a b) c := by
        have d2: b ∣ lcm a b := by
          apply dvd_lcm_right
        have d3: lcm a b ∣ lcm (lcm a b) c := by
          apply dvd_lcm_left
        apply dvd_trans d2 d3
      have d4: lcm (lcm a b) c ∣ lcm (lcm (lcm a b) c) d := by
        apply dvd_lcm_left
      apply dvd_trans d1 d4
    have hc': c ∣ l := by --show c ∣ l
      rw [hl]
      have d1: c ∣ lcm (lcm a b) c := by
         apply dvd_lcm_right
      have d2: lcm (lcm a b) c ∣ lcm (lcm (lcm a b) c) d := by
         apply dvd_lcm_left
      apply dvd_trans d1 d2
    have hd': d ∣ l := by --show d ∣ l
      rw [hl]
      apply dvd_lcm_right
    have nel: lcm (lcm (lcm a b) c) d ≠ 0 := by  --show that l ≠ 0
      have nel': (lcm (lcm (lcm a b) c) d).natAbs ≠ 0 := by
        rw [show (lcm (lcm (lcm a b) c) d).natAbs = (lcm (lcm a b) c).lcm d by rw [Int.natAbs_lcm]]
        apply Int.lcm_ne_zero
        have nel2: (lcm (lcm a b) c).natAbs ≠ 0 := by
          rw [show (lcm (lcm a b) c).natAbs = (lcm a b).lcm c by rw [Int.natAbs_lcm]]
          apply Int.lcm_ne_zero
          have nel3: (lcm a b).natAbs ≠ 0 := by
            rw [show (lcm a b).natAbs = a.lcm b by rw [Int.natAbs_lcm]]
            apply Int.lcm_ne_zero
            omega
            omega
          simp [nel3]
          omega
          omega
        simp [nel2]
        omega
        omega
      simp [nel']
      omega
    have l_pos: 0 < l := by  -- show 0 < l
      rw [hl]
      rw [← Int.coe_lcm]
      simp
      by_contra! no
      replace no: (lcm (lcm a b) c).lcm d = 0 := by omega
      rw [← Int.coe_lcm] at nel
      simp at nel
      simp [no] at nel
    clear nel
    have posa': 0 < a' := by
      apply Int.ediv_pos_of_pos_of_dvd
      all_goals omega
    have posb': 0 < b' := by
      apply Int.ediv_pos_of_pos_of_dvd
      all_goals omega
    have posc': 0 < c' := by  -- show 0 < c'
      apply Int.ediv_pos_of_pos_of_dvd
      all_goals omega
    have posd': 0 < d' := by  -- show 0 < d'
      apply Int.ediv_pos_of_pos_of_dvd
      all_goals omega
    have eq: (1: ℝ) / a' + 1 / b' = 1 / c' + 1 / d' := by
      simp [a', b', c', d']
      field_simp
      rw [show (a: ℝ) + (b: ℝ) = ↑((a: ℤ) + b) by simp]
      rw [show (c: ℝ) + (d: ℝ) = ↑((c: ℤ) + d) by simp]
      rw [h2]
    set T:= (1: ℝ) / a' + 1 / b' with hT
    have hda': a' < d' := by  -- show that a' < d', a little bit tricky in lean4
      simp [a',d']
      have o: (l: ℚ) / a < (l: ℚ) / d := by
        apply div_lt_div_of_pos_left
        simp
        omega
        simp
        omega
        simp
        omega
      have j: (l: ℚ) / (a: ℚ) = ↑((l: ℤ) / (a: ℤ)) := by
        rw [← Rat.intCast_div]
        exact ha'
      have k: (l: ℚ) / (d: ℚ) = ↑((l: ℤ) / (d: ℤ)) := by
        rw [← Rat.intCast_div]
        exact hd'
      rw [j, k] at o
      simp at o
      exact o
    have hab': b' < a' := by  -- show that a' < b'
      simp [a',b']
      have o: (l: ℚ) / b < (l: ℚ) / a := by
        apply div_lt_div_of_pos_left
        simp
        omega
        simp
        omega
        simp
        omega
      have j: (l: ℚ) / (a: ℚ) = ↑((l: ℤ) / (a: ℤ)) := by
        rw [← Rat.intCast_div]
        exact ha'
      have k: (l: ℚ) / (b: ℚ) = ↑((l: ℤ) / (b: ℤ)) := by
        rw [← Rat.intCast_div]
        exact hb'
      rw [j, k] at o
      simp at o
      exact o
    have hbc': c' < b' := by  -- show that b' < c'
      simp [b',c']
      have o: (l: ℚ) / c < (l: ℚ) / b := by
        apply div_lt_div_of_pos_left
        simp
        omega
        simp
        omega
        simp
        omega
      have j: (l: ℚ) / (b: ℚ) = ↑((l: ℤ) / (b: ℤ)) := by
        rw [← Rat.intCast_div]
        exact hb'
      have k: (l: ℚ) / (c: ℚ) = ↑((l: ℤ) / (c: ℤ)) := by
        rw [← Rat.intCast_div]
        exact hc'
      rw [j, k] at o
      simp at o
      exact o
    clear posa' posb' posd'  -- now 0 < c' < b' < a' < d'
    have eq2: a + b = T * l := by
      rw [hT]
      simp [a',b']
      field_simp
    have hc1: 2 ≤ c' := by  -- we show that c' ≥ 2
      by_contra! hd1
      replace hc1: c' = 1 := by omega
      have l1: T ≤ (1: ℝ) / 2 + (1: ℝ) / 3 := by
        rw [hT]
        have o1: 2 ≤ b' := by omega
        have o2: 3 ≤ a' := by omega
        replace o1: 2 ≤ (b': ℝ) := by norm_cast
        replace o2: 3 ≤ (a': ℝ) := by norm_cast
        have la: 1 / (a': ℝ) ≤ 1 / 3 := by
           rw [div_le_div_iff_of_pos_left]
           exact o2
           norm_num
           simp
           omega
           simp
        have lb: 1 / (b': ℝ) ≤ 1 / 2 := by
           rw [div_le_div_iff_of_pos_left]
           exact o1
           norm_num
           simp
           omega
           simp
        nlinarith
      have l2: 1 ≤ T := by
        rw [eq]
        simp [hc1]
        omega
      have contra: 1 ≤ (1: ℝ) / 2 + 1 / 3 := by
        calc
          1 ≤ T := l2
          _ ≤ (1: ℝ) / 2 + (1: ℝ) / 3 := l1
      absurd contra
      norm_num
    have hb1: 3 ≤ b' := by omega
    have ha1: 4 ≤ a' := by omega
    by_cases ha2: a' = 4
    -- for the cases a' = 4, we show that T = 7/12, l ≤ 996
    . replace hb1: b' = 3 := by omega
      replace hc1: c' = 2 := by omega
      simp [ha2,hb1] at hT
      rw [show 4⁻¹ + 3⁻¹ = (7: ℝ) / 12 by norm_num] at hT
      rw [hT] at eq2
      have ll: l ≤ 996 := by
        have dvd1: 4 ∣ l := by
          have o: l = a * a' := by
            simp [a']
            qify
            rw [Rat.intCast_div]
            have ne: (a: ℚ) ≠ 0 := by
              qify at hd hda
              linarith
            field_simp
            exact ha'
          rw [o]
          rw [ha2]
          omega
        by_contra! no
        have l_val: l = 997 ∨ l = 998 ∨ l = 999 := by
          omega
        clear * - l_val dvd1
        rcases l_val with u | u | u
        all_goals simp [u] at dvd1; absurd dvd1; norm_num
      have i: ↑a + ↑b ≤ (581: ℝ) := by
          rw [eq2]
          replace ll: (l: ℝ) ≤ 996 := by
            clear * - ll
            rify at ll
            exact ll
          nlinarith [ll]
      rify
      exact i
     -- for the cases a' > 4, we show that a + b < 581
    . replace ha2: 5 ≤ a' := by omega
      have lT: T ≤ 8 / 15 := by
        rw [hT]
        have l1: 1 / (a': ℝ) ≤ 1 / 5 := by
          rw [div_le_div_iff_of_pos_left]
          rify at ha2
          exact ha2
          norm_num
          simp
          omega
          simp
        have l2: 1 / (b': ℝ) ≤ 1 / 3 := by
          rw [div_le_div_iff_of_pos_left]
          rify at hb1
          exact hb1
          norm_num
          simp
          omega
          simp
        nlinarith
      have i: ↑a + ↑b < (534: ℝ) := by
        rw [eq2]
        have ll: (l: ℝ) < 1000 := by
          clear * - h1
          rify at h1
          exact h1
        calc
           T * ↑l ≤ (8 / 15) * ↑l := by rw [mul_le_mul_right]; exact lT; rify at l_pos; exact l_pos
                _ < 8 / 15 * 1000 := by nlinarith [ll]
                _ < 534 := by norm_num
      rify
      linarith