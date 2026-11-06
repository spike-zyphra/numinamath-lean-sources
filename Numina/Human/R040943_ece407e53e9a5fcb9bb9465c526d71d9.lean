import Mathlib

/-Let a, b, c, d, e be five distinct integers for which:
    (4 - a) * (4 - b) * (4 - c) * (4 - d) * (4 - e) = 12
  Prove that a + b + c + d + e = 17-/

theorem algebra_239305 (a b c d e : ℤ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : d < e) (h : (4 - a) * (4 - b) * (4 - c) * (4 - d) * (4 - e) = 12) :
    a + b + c + d + e = 17 := by

  -- for convenience, we set x = 4 - a, y = 4 - b, z = 4 - c, w = 4 - d, v = 4 - e
    set x:= 4 - a
    set y:= 4 - b
    set z:= 4 - c
    set w:= 4 - d
    set v:= 4 - e

    replace h₀: y < x := by
      simp [x, y]
      linarith
    replace h₁: z < y := by
      simp [y, z]
      linarith
    replace h₂: w < z := by
      simp [z, w]
      linarith
    replace h₃: v < w := by
      simp [w, v]
      linarith

    -- we show that x + y + z + w + v = 3
    have r: x + y + z + w + v = 3 := by
      clear_value x y z w v

      -- we show that there is only one solution to the equation by determine the sign of each variable
      have s: x = 3 ∧ y = 2 ∧ z = 1 ∧ w = -1 ∧ v = -2 := by

        -- show v < 0
          have lv: v < 0 := by
            by_contra! o
            replace lv: 1 ≤ v := by
              by_contra! p
              have q: v = 0 := by omega
              simp [q] at h
            have lw: 2 ≤ w := by linarith
            have lz: 6 ≤ w * z := by nlinarith
            have ly: 24 ≤ w * z * y := by nlinarith
            have lx: 120 ≤ w * z * y * x := by nlinarith
            have c: 120 ≤ 12 := by
              zify
              rw [← h]
              nlinarith
            norm_num at c

          -- show w < 0
          have lw: w < 0 := by
            by_contra! o
            replace lw: 0 < w := by
              by_contra! p
              have q: w = 0 := by omega
              simp [q] at h
            have lw: w * v < 0 := by nlinarith
            have lz: w * v * z < 0 := by nlinarith
            have ly: w * z * v * y < 0:= by nlinarith
            have lx: x * y * z * w * v < 0 := by nlinarith
            simp [h] at lx

          -- show 0 < z
          have lz: 0 < z := by
            by_contra! o
            replace lz: z < 0 := by
              by_contra! p
              have q: z = 0 := by omega
              simp [q] at h
            -- then we have y < 0
            have ly: y < 0 := by
              by_contra! p
              replace ly: 0 < y := by
                by_contra! q
                have r: y = 0 := by omega
                simp [r] at h
              have lx: 0 < x := by linarith
              have l1: 0 < x * y := by nlinarith
              have l2: x * y * z < 0 := by nlinarith
              have l3: 0 < x * y * z * w := by nlinarith
              have l4: x * y * z * w * v < 0 := by nlinarith
              simp [h] at l4
            set y':= -y
            set z':= -z
            set w':= -w
            set v':= -v
            replace lv: 4 ≤ v' := by
              simp [v']
              nlinarith
            replace lw: 12 ≤ v' * w' := by
              simp [w']
              nlinarith
            replace lz: 24 ≤ z' * v' * w'  := by
              simp [z']
              nlinarith
            replace ly: 24 ≤ y' * z' * v' * w' := by
              simp [y']
              nlinarith
            clear o
            simp [y', z', w', v'] at ly
            have lx: x ≤ -1 ∨ 1 ≤ x := by
              have t: x ≠ 0 := by
                by_contra! o
                simp [o] at h
              omega
            rcases lx with o | o
            .
              clear * - o ly h
              nlinarith
            .
              clear * - o ly h
              nlinarith

          -- then we can write in the term of postive integers
          set w':= -w with hw
          set v':= -v with hv
          replace lw: 0 < w' := by
            simp [w']
            linarith
          replace lv: 0 < v' := by
            simp [v']
            linarith
          replace hw: w = - w' := by
            simp [w']
          replace hv: v = - v' := by
            simp [v']
          simp [hw, hv] at *
          clear_value w' v'
          clear h₂ hw hv

          -- we first show that x = 3
          have ex: x = 3 := by
            have lx1: 3 ≤ x := by nlinarith
            have lx2: x ≤ 3 := by
              by_contra! o
              have ly: 6 < x * y := by nlinarith
              have lz: 6 < x * y * z := by nlinarith
              have lw: 6 < x * y * z * w' := by nlinarith
              have lv: 12 < x * y * z * w' * v' := by nlinarith
              rw [h] at lv
              norm_num at lv
            omega
          simp [ex] at *
          replace h: y * z * w' * v' = 4 := by
            rw [show 3 * y * z * w' * v' = 3* (y * z * w' * v') by nlinarith] at h
            omega

          -- then it's easy to derive the rest
          have ey: y = 2 := by omega
          have ez: z = 1 := by omega
          simp [ey,ez] at *
          rw [show 2 * w' * v' = 2 * (w' * v') by ring] at h
          replace h: w' * v' = 2 := by omega
          have ew: w' < 2 := by nlinarith
          replace ew: w' = 1 := by
            omega
          simp [ew] at h
          simp [ew,h]

      simp [s]


    -- finally, use r to obtain the result
    simp [x, y, z, w, v] at r
    linarith

