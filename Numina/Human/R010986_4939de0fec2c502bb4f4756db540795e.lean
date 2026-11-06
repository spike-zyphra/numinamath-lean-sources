import Mathlib

/-Find the smallest positive integer c such that c=ab, where a=x^3+y^3 and
b=x^3+y ^3each have solutions in integers (x,y), but c=x^3+y^3 does not. -/
theorem number_theory_611141: IsLeast {c: ℤ | c > 0 ∧ ¬ (∃ x y: ℤ, c = x^3 + y^3) ∧
 (∃ a b : ℤ, c = a * b ∧ ∃ x1 y1: ℤ, a = x1 ^ 3 + y1 ^ 3 ∧ ∃ x2 y2, b = x2 ^ 3 + y2 ^ 3)} 4:= by
  -- we first show a lemma which will be used many times
  have ne_3: ¬ ∃ x y: ℤ, 3 = x^3 + y^3 := by
      by_contra! h
      obtain ⟨x,y,h⟩ := h
      have hx: x > 0 := by
          by_contra! hx
          have hy: y > 0 := by
            by_contra! hy
            have contra: (3: ℤ) ≤ 0 := by
              rw [h]
              replace hx: x ^ 3 ≤ 0 := by
                have o: x ^ 3 = x ^ 2 * x := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ x ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              replace hy: y ^ 3 ≤ 0 := by
                have o: y ^ 3 = y ^ 2 * y := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ y ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              omega
            tauto
          set a:= -x with ha
          replace ha: x = -a := by omega
          simp [ha] at h
          simp [ha] at hx
          rw [show (-a) ^ 3 = - (a ^ 3) by ring] at h
          rw [show -a ^ 3 + y ^ 3 = (y - a) * (y ^ 2 + a * y + a ^ 2) by ring_nf] at h
          have o1: 0 ≤ y ^ 2 + a * y + a ^ 2 := by nlinarith
          have o: y - a ≥ 0 := by nlinarith
          have o2: y - a ≠ 0 := by nlinarith
          replace o2: y - a ≥ 1 := by omega
          have h2: 4 ≥ y ^ 2 + a * y + a ^ 2 := by
            nlinarith
          by_cases l: a = 0
          -- a = 0
          . simp [l] at h
            have t: y < 2 := by
              by_contra! t
              have contra: (8: ℤ) ≤ 3 := by
                have s: 2 ^ 2 ≤ y ^ 2 := by nlinarith
                calc
                  8 = 2 * 2 ^ 2 := by norm_num
                  _ ≤ y * 2 ^ 2 := by omega
                  _ ≤ y * y ^ 2 := by nlinarith
                  _ = 3 := by omega
              tauto
            replace t: y = 1 := by omega
            simp [t] at h
          -- a ≠ 0
          . replace l: 1 ≤ a := by omega
            replace hy: 2 ≤ y := by linarith
            have contra: y ^ 2 + a * y + a ^ 2 ≥ 5 := by nlinarith
            nlinarith

        -- we show we must have y > 0 by the similar argument
      have hy: y > 0 := by
          by_contra! hy
          have hx: x > 0 := by
            by_contra! hx
            have contra: (3: ℤ) ≤ 0 := by
              rw [h]
              replace hy: y ^ 3 ≤ 0 := by
                have o: y ^ 3 = y ^ 2 * y := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ y ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              replace hy: x ^ 3 ≤ 0 := by
                have o: x ^ 3 = x ^ 2 * x := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ x ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              omega
            tauto
          set a:= -y with ha
          replace ha: y = -a := by omega
          simp [ha] at h
          simp [ha] at hy
          rw [show (-a) ^ 3 = - (a ^ 3) by ring] at h
          rw [show x ^ 3 + -a ^ 3 = (x - a) * (x ^ 2 + a * x + a ^ 2) by ring_nf] at h
          have o1: 0 ≤ x ^ 2 + a * x + a ^ 2 := by nlinarith
          have o: x - a ≥ 0 := by nlinarith
          have o2: x - a ≠ 0 := by nlinarith
          replace o2: x - a ≥ 1 := by omega
          have h2: 4 ≥ x ^ 2 + a * x + a ^ 2 := by
            nlinarith
          by_cases l: a = 0
          -- a = 0
          . simp [l] at h
            have t: x < 2 := by
              by_contra! t
              have contra: (8: ℤ) ≤ 3 := by
                have s: 2 ^ 2 ≤ x ^ 2 := by nlinarith
                calc
                  8 = 2 * 2 ^ 2 := by norm_num
                  _ ≤ x * 2 ^ 2 := by omega
                  _ ≤ x * x ^ 2 := by nlinarith
                  _ = 3 := by omega
              tauto
            replace t: x = 1 := by omega
            simp [t] at h
          -- a ≠ 0
          . replace l: 1 ≤ a := by omega
            replace hy: 2 ≤ x := by linarith
            have contra: x ^ 2 + a * x + a ^ 2 ≥ 5 := by nlinarith
            nlinarith

      have hx2: x < 2 := by
          by_contra! hx2
          have contra: x ^ 3 + y ^ 3 ≥ 8 := by
            have o: y ^ 3 ≥ 0 := by
              apply pow_nonneg
              omega
            calc
              x ^ 3 + y ^ 3 ≥ x ^ 3 := by nlinarith
                          _ ≥ 2 ^ 3 := by simp; rw [show (8: ℤ) = 2 ^ 3 by norm_num]; rw [pow_le_pow_iff_left₀]; omega; omega; omega; omega
                          _ = 8 := by norm_num
          nlinarith
      replace hx2: x = 1 := by omega
      simp [hx2] at h
      replace h: y ^ 3 = 2 := by nlinarith
      have hy2: y < 2 := by
          by_contra! hy2
          have contra: 8 ≤ y ^ 3 := by
            calc
              8 = 2 ^ 3 := by norm_num
              _ ≤ y ^ 3 := by rw [pow_le_pow_iff_left₀]; omega; omega; omega; omega
          nlinarith
      replace hy2: y = 1 := by omega
      rw [hy2] at h
      tauto

  -- we now show the main theorem
  constructor
  -- the forward direction
  . simp only [Set.mem_setOf_eq]
    constructor
    . norm_num
    . constructor
      . simp
        intro x y h
        -- similar with the proof of lemma
        -- we show we must have x > 0
        have hx: x > 0 := by
          by_contra! hx
          have hy: y > 0 := by
            by_contra! hy
            have contra: (4: ℤ) ≤ 0 := by
              rw [h]
              replace hx: x ^ 3 ≤ 0 := by
                have o: x ^ 3 = x ^ 2 * x := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ x ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              replace hy: y ^ 3 ≤ 0 := by
                have o: y ^ 3 = y ^ 2 * y := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ y ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              omega
            tauto
          set a:= -x with ha
          replace ha: x = -a := by omega
          simp [ha] at h
          simp [ha] at hx
          rw [show (-a) ^ 3 = - (a ^ 3) by ring] at h
          rw [show -a ^ 3 + y ^ 3 = (y - a) * (y ^ 2 + a * y + a ^ 2) by ring_nf] at h
          have o1: 0 ≤ y ^ 2 + a * y + a ^ 2 := by nlinarith
          have o: y - a ≥ 0 := by nlinarith
          have o2: y - a ≠ 0 := by nlinarith
          replace o2: y - a ≥ 1 := by omega
          have h2: 4 ≥ y ^ 2 + a * y + a ^ 2 := by
            nlinarith
          by_cases l: a = 0
          -- a = 0
          . simp [l] at h
            have t: y < 2 := by
              by_contra! t
              have contra: (8: ℤ) ≤ 4 := by
                have s: 2 ^ 2 ≤ y ^ 2 := by nlinarith
                calc
                  8 = 2 * 2 ^ 2 := by norm_num
                  _ ≤ y * 2 ^ 2 := by omega
                  _ ≤ y * y ^ 2 := by nlinarith
                  _ = 4 := by omega
              tauto
            replace t: y = 1 := by omega
            simp [t] at h
          -- a ≠ 0
          . replace l: 1 ≤ a := by omega
            replace hy: 2 ≤ y := by linarith
            have contra: y ^ 2 + a * y + a ^ 2 ≥ 5 := by nlinarith
            nlinarith

        -- we show we must have y > 0 by the similar argument
        have hy: y > 0 := by
          by_contra! hy
          have hx: x > 0 := by
            by_contra! hx
            have contra: (4: ℤ) ≤ 0 := by
              rw [h]
              replace hy: y ^ 3 ≤ 0 := by
                have o: y ^ 3 = y ^ 2 * y := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ y ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              replace hy: x ^ 3 ≤ 0 := by
                have o: x ^ 3 = x ^ 2 * x := by
                  rw [show 3 = 2 + 1 by norm_num]
                  rw [pow_add]
                  ring
                rw [o]
                have o1: 0 ≤ x ^ 2 := by
                  apply sq_nonneg
                apply Int.mul_nonpos_of_nonneg_of_nonpos
                all_goals omega
              omega
            tauto
          set a:= -y with ha
          replace ha: y = -a := by omega
          simp [ha] at h
          simp [ha] at hy
          rw [show (-a) ^ 3 = - (a ^ 3) by ring] at h
          rw [show x ^ 3 + -a ^ 3 = (x - a) * (x ^ 2 + a * x + a ^ 2) by ring_nf] at h
          have o1: 0 ≤ x ^ 2 + a * x + a ^ 2 := by nlinarith
          have o: x - a ≥ 0 := by nlinarith
          have o2: x - a ≠ 0 := by nlinarith
          replace o2: x - a ≥ 1 := by omega
          have h2: 4 ≥ x ^ 2 + a * x + a ^ 2 := by
            nlinarith
          by_cases l: a = 0
          -- a = 0
          . simp [l] at h
            have t: x < 2 := by
              by_contra! t
              have contra: (8: ℤ) ≤ 4 := by
                have s: 2 ^ 2 ≤ x ^ 2 := by nlinarith
                calc
                  8 = 2 * 2 ^ 2 := by norm_num
                  _ ≤ x * 2 ^ 2 := by omega
                  _ ≤ x * x ^ 2 := by nlinarith
                  _ = 4 := by omega
              tauto
            replace t: x = 1 := by omega
            simp [t] at h
          -- a ≠ 0
          . replace l: 1 ≤ a := by omega
            replace hy: 2 ≤ x := by linarith
            have contra: x ^ 2 + a * x + a ^ 2 ≥ 5 := by nlinarith
            nlinarith

        have hx2: x < 2 := by
          by_contra! hx2
          have contra: x ^ 3 + y ^ 3 ≥ 8 := by
            have o: y ^ 3 ≥ 0 := by
              apply pow_nonneg
              omega
            calc
              x ^ 3 + y ^ 3 ≥ x ^ 3 := by nlinarith
                          _ ≥ 2 ^ 3 := by simp; rw [show (8: ℤ) = 2 ^ 3 by norm_num]; rw [pow_le_pow_iff_left₀]; omega; omega; omega; omega
                          _ = 8 := by norm_num
          nlinarith
        replace hx2: x = 1 := by omega
        simp [hx2] at h
        replace h: y ^ 3 = 3 := by nlinarith
        have hy2: y < 2 := by
          by_contra! hy2
          have contra: 8 ≤ y ^ 3 := by
            calc
              8 = 2 ^ 3 := by norm_num
              _ ≤ y ^ 3 := by rw [pow_le_pow_iff_left₀]; omega; omega; omega; omega
          nlinarith
        replace hy2: y = 1 := by omega
        rw [hy2] at h
        tauto

      . use 2
        use 2
        constructor
        . norm_num
        . use 1
          use 1
          norm_num
          use 1
          use 1
          norm_num

    -- the backward direction
  . intro c
    intro h
    by_contra! no
    simp at h
    rcases h with ⟨hc,h⟩
    have c_val: c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases c_val with l | l | l
    -- c = 1
    . simp [l] at h
      rcases h with ⟨h1,h2⟩
      absurd h1
      simp
      use 1
      use 0
      norm_num
    -- c = 2
    . simp [l] at h
      rcases h with ⟨h1,h2⟩
      absurd h1
      simp
      use 1
      use 1
      norm_num
    -- c = 3
    . simp [l] at h
      rcases h with ⟨h1,h2⟩
      absurd h2
      simp
      intro a b h
      intro x1 y1 h3
      clear no hc l h1 h2
      have o: a = 3 ∧ b = 1 ∨ a = 1 ∧ b = 3 ∨ a = -1 ∧ b = -3 ∨ a = -3 ∧ b = -1 := by
        clear * - h
        have l: a ≥ 0 ∧ b > 0 ∨ a < 0 ∧ b < 0 := by
          by_contra! no
          rcases no with ⟨l1,l2⟩
          by_cases g: a ≥ 0
          . simp [g] at l1
            nlinarith
          . simp at g
            simp [g] at l2
            nlinarith
        rcases l with ⟨l1,l2⟩ | ⟨l1,l2⟩
        . have ha: a < 4 := by nlinarith
          interval_cases a
          all_goals omega
        . have ha: a > -4 := by nlinarith
          interval_cases a
          all_goals omega
      rcases o with ⟨o1,o2⟩ | ⟨o1,o2⟩ | ⟨o1,o2⟩ | ⟨o1,o2⟩
      -- a = 3, b = 1
      . simp [o2]
        simp [o1] at h3
        absurd ne_3
        use x1
        use y1
      -- a = 1, b = 3
      . simp [o2]
        by_contra! no
        simp [ne_3] at no
      -- a = -1, b = -3
      . simp [o2]
        by_contra! no
        obtain ⟨x,y,no⟩ := no
        set t:= -x with ht
        set s:= -y with hs
        replace ht: x = -t := by omega
        replace hs: y = -s := by omega
        simp [ht,hs] at no
        rw [show (-t) ^ 3 = - (t ^ 3) by ring] at no
        rw [show (-s) ^ 3 = - (s ^ 3) by ring] at no
        replace no: 3 = t ^ 3 + s ^ 3 := by omega
        absurd ne_3
        use t
        use s
      -- a = -3, b = -1
      . simp [o1] at h3
        set t:= -x1 with ht
        set s:= -y1 with hs
        replace ht: x1 = -t := by omega
        replace hs: y1 = -s := by omega
        simp [ht,hs] at h3
        rw [show (-t) ^ 3 = - (t ^ 3) by ring] at h3
        rw [show (-s) ^ 3 = - (s ^ 3) by ring] at h3
        replace no: 3 = t ^ 3 + s ^ 3 := by omega
        absurd ne_3
        use t
        use s
