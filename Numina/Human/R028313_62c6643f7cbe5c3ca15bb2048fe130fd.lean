import Mathlib

/- 2. Each of the equations $a x^{2}-b x+c=0$ and $c x^{2}-a x+b=0$ has two distinct real roots.
The sum of the roots of the first equation is non-negative,
and the product of the roots of the first equation is 9 times the sum of the roots of the second equation.
Find the ratio of the sum of the roots of the first equation to the product of the roots of the second equation. -/

theorem algebra_115337 {a b c x1 x2 x3 x4: ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h_ne_1: x1 ≠ x2)
    (h_ne_2: x3 ≠ x4) (hx1 : a * x1^2 - b * x1 + c = 0) (hx2 : a * x2^2 - b * x2 + c = 0)
    (hx3 : c * x3^2 - a * x3 + b = 0) (hx4 : c * x4^2 - a * x4 + b = 0)
    (hsum : x1 + x2 ≥ 0) (hprod : x1 * x2 = 9 * (x3 + x4)) :
    (x1 + x2) / (x3 * x4) = -3 := by

    have s1: x1 + x2 = b / a := by  -- apply Vieta's formula
      have o1: a * x1^2 - b * x1 + c - (a * x2^2 - b * x2 + c) = 0 := by
        rw [hx1, hx2]
        ring
      rw [show a * x1^2 - b * x1 + c - (a * x2^2 - b * x2 + c) = (x1 - x2) * (a * (x1 + x2) - b) by ring] at o1
      simp at o1
      have s: x1 - x2 ≠ 0 := by
        by_contra! s
        replace s: x1 = x2 := by linarith
        simp [s] at h_ne_1
      simp [s] at o1
      field_simp [o1]
      linarith

    have s2: x3 + x4 = a / c := by  -- apply Vieta's formula
      have o1: c * x3^2 - a * x3 + b - (c * x4^2 - a * x4 + b) = 0 := by
        rw [hx3, hx4]
        ring
      rw [show c * x3^2 - a * x3 + b - (c * x4^2 - a * x4 + b) = (x3 - x4) * (c * (x3 + x4) - a) by ring] at o1
      simp at o1
      have s: x3 - x4 ≠ 0 := by
        by_contra! s
        replace s: x3 = x4 := by linarith
        simp [s] at h_ne_2
      simp [s] at o1
      field_simp [o1]
      linarith

    have p1: x1 * x2 = c / a := by  -- apply Vieta's formula
        replace s1: x2 = b / a - x1 := by
            linarith
        simp [s1]
        field_simp
        nlinarith [hx1]

    have p2: x3 * x4 = b / c := by  -- apply Vieta's formula
        replace s2: x4 = a / c - x3 := by
            linarith
        simp [s2]
        field_simp
        nlinarith [hx3]

    have l1: 0 ≤ b ^ 2 - 4 * a * c := by   -- 0 ≤ delta
        have eq: b ^ 2 - 4 * a * c = a ^ 2 * (x1 - x2) ^ 2 := by
            rw [show (x1 - x2) ^ 2 = (x1 + x2) ^ 2 - 4 * (x1 * x2) by ring]
            simp [s1,p1]
            field_simp
            ring
        simp [eq]
        rw [show a ^ 2 * (x1 - x2) ^ 2 = (a * (x1 - x2)) ^ 2 by ring]
        apply sq_nonneg


    have l2: 0 ≤ a ^ 2 - 4 * b * c := by   -- 0 ≤ delta
        have eq: a ^ 2 - 4 * b * c = c ^ 2 * (x3 - x4) ^ 2 := by
            rw [show (x3 - x4) ^ 2 = (x3 + x4) ^ 2 - 4 * (x3 * x4) by ring]
            simp [s2,p2]
            field_simp
            ring
        simp [eq]
        rw [show c ^ 2 * (x3 - x4) ^ 2 = (c * (x3 - x4)) ^ 2 by ring]
        apply sq_nonneg

    rw [p1,s2] at hprod
    rw [s1,p2]
    field_simp
    replace hprod: c ^ 2 = (3 * a) ^ 2 := by
        rw [show a / c = (c / a)⁻¹ by field_simp] at hprod
        field_simp at hprod
        linarith
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hprod
    rcases hprod with h | h
    -- cases: c = 3 * a, we show contradiction by inequality
    .
        rw [s1] at hsum
        simp [h] at *
        clear hc h
        clear * - l1 l2 hsum ha hb
        set t:= b / a with ht
        have o1: 12 ≤ t ^ 2 := by
            simp [ht]
            field_simp
            have o: a ^ 2 ≠ 0 := by
                by_contra! o
                simp at o
                tauto
            rw [le_div_iff₀]
            nlinarith
            have o2: 0 ≤ a ^ 2 := by
                apply sq_nonneg
            by_contra! no
            have q: a ^ 2 = 0 := by linarith
            simp at q
            tauto
        have o2: 0 ≤ 1 - 12 * t := by
            simp [ht]
            field_simp
            by_cases ua: 0 < a
            .
                rw [div_le_one₀]
                ring_nf at l2
                replace l2: a * (12 * b - a) ≤ 0 := by
                    nlinarith
                have i: 12 * b - a ≤ 0 := by
                    apply nonpos_of_mul_nonpos_right l2 ua
                linarith
                exact ua
            .
                rw [show 12 * b / a = 12 * (- b) / (- a) by field_simp]
                rw [div_le_one₀]
                ring_nf at l2
                replace ua: 0 < -a := by
                    simp at ua
                    replace ua: 0 ≤ -a := by linarith
                    by_contra! no
                    replace no: a = 0 := by linarith
                    simp at no
                    tauto
                replace l2: (-a) * (12 * -b - (-a)) ≤ 0 := by
                    nlinarith
                have i: 12 * -b - (-a) ≤ 0 := by
                    apply nonpos_of_mul_nonpos_right l2 ua
                linarith
                simp at ua
                replace ua: 0 ≤ -a := by linarith
                by_contra! no
                replace no: a = 0 := by linarith
                simp at no
                tauto
        nlinarith  -- the inequality is not satisfied

    -- cases: c = -3 * a
    .
        simp [h]
        ring