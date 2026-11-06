import Mathlib

/-Writing 1989 in base b, we obtain a three-digit number: xyz.
It is known that the sum of the digits is the same in base 10
and in base b, that is,
1+9+8+9=x+y+z. Determine x,y,z,b.-/

theorem number_Theory_56714
: {(x, y, z, b): ℤ × ℤ × ℤ × ℤ | 1 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧
  x < b ∧ y < b ∧ z < b ∧ 2 ≤ b ∧ x * b ^ 2 + y * b + z = 1989 ∧ x + y + z = 1 + 9 + 8 + 9}
  = {(5, 9, 13, 19)} := by

    ext ⟨x, y, z, b⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨hx, hy, hz, lx, ly, lz, hb, h1, h2⟩

      -- we show that b - 1 ∣ p (b) - p (1)
      have d: b - 1 ∣ (x * b ^ 2 + y * b + z) - (x + y + z) := by
        rw [show (x * b ^ 2 + y * b + z) - (x + y + z) = (b - 1) * (x * (b + 1) + y) by ring]
        simp

      -- then we conclude that b - 1 ∣ 1962 = 2 * 9 * 109
      replace d: b - 1 ∣ 1962 := by
        simp [h1, h2] at d
        exact d

      -- then we can prove that b = 19
      have vb: b = 19 := by
        have lb: b ^ 2 ≤ 1989 := by
          rw [← h1]
          nlinarith
        replace lb: b < 45 := by nlinarith
        have rb: 10 < b := by nlinarith

        -- for convenience, we prove in ℕ
        set p:= (b - 1).natAbs
        have vp: p = 18 := by
          have lp: 9 < p := by
            simp [p]
            zify
            rw [show |b - 1| = b - 1 by apply abs_of_nonneg; omega]
            linarith
          have rp: p < 44 := by
            simp [p]
            zify
            rw [show |b - 1| = b - 1 by apply abs_of_nonneg; omega]
            linarith
          rw [← Int.natAbs_dvd_natAbs] at d
          rw [show (b - 1).natAbs = p by simp [p]] at d
          simp at d
          clear * - lp rp d
          clear_value p
          replace d: p ∈ Nat.divisors 1962 := by
            simp
            exact d
          have eq: Nat.divisors 1962 = {1, 2, 3, 6, 9, 18, 109, 218, 327, 654, 981, 1962} := by
            native_decide
          rw [eq] at d
          clear eq
          simp at d
          rcases d with d | d | d | d | d | d | d | d | d | d | d | d
          all_goals omega

        -- turn back to ℤ
        simp [p] at vp
        zify at vp
        rw [show |b - 1| = b - 1 by apply abs_of_nonneg; omega] at vp
        linarith


      -- finally, use the value of b to derive x, y, z
      simp [vb] at h1 lx ly lz
      have lx1: x < 6 := by nlinarith
      have lx2: x > 4 := by nlinarith
      have vx: x = 5 := by omega
      simp [vx] at h1 h2
      replace h1: y * 19 + z = 184 := by omega
      have ly1: y < 10 := by nlinarith
      have ly2: y > 8 := by nlinarith
      have vy: y = 9 := by omega
      simp [vy] at h2
      have vz: z = 13 := by omega
      simp [vx, vy, vz, vb]



    -- the backward direction
    .
      intro h
      simp at h
      simp [h]