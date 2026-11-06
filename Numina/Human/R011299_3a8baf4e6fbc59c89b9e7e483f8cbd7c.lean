import Mathlib

-- we write the solution as a lemma
lemma lemma_1 (x y z w: ℤ) (hxy: y < x) (hxz: z < y) (hwx: w < z) (h: x * y * z * w = 4):
  x + y + z + w = 0 := by

    -- we begin by showing that w and z are negative, while x and y are positive
    -- we show that w < 0
    have lw: w < 0 := by
      by_contra! lw
      replace lw: 1 ≤ w := by
        by_contra! o
        replace o: w = 0 := by
          omega
        simp [o] at h
      have lz: 2 ≤ z := by
        omega
      have ly: 3 ≤ y := by
        omega
      have lx: 4 ≤ x := by
        omega
      have f1: 12 ≤ x * y := by nlinarith
      have f2: 12 ≤ x * y * z := by
        nlinarith
      have f3: 12 ≤ x * y * z * w := by
        nlinarith
      simp [h] at f3

    -- we then show that z < 0
    have lz: z < 0 := by
      by_contra! lz
      replace lz: 1 ≤ z := by
        by_contra! o
        replace o: z = 0 := by
          omega
        simp [o] at h
      have ly: 2 ≤ y := by
        omega
      have lx: 3 ≤ x := by
        omega
      have f1: 6 ≤ x * y := by nlinarith
      have f2: 6 ≤ x * y * z := by
        nlinarith
      have f3: 6 ≤ x * y * z * w := by
        nlinarith
      simp [h] at f3

    -- we show that 0 < y
    have ly: 0 < y := by
      by_contra! ly
      replace ly: y < 0 := by
        by_contra! o
        replace o: y = 0 := by
          omega
        simp [o] at h
      -- then we must have x < 0
      have lx: x < 0 := by
        rw [show x * y * z * w = x * (y * z * w) by ring] at h
        have o: y * z * w < 0 := by
          have o1: 0 < y * z := by
            apply Int.mul_pos_of_neg_of_neg
            exact ly
            exact lz
          nlinarith
        replace h: 0 < x * (y * z * w) := by
          simp [h]
        rw [neg_iff_neg_of_mul_pos h]
        exact o
      replace lx: x ≤ -1 := by omega
      replace ly: y ≤ -2 := by
        omega
      replace lz: z ≤ -3 := by
        omega
      replace lw: w ≤ -4 := by
        omega
      have f1: 2 ≤ x * y := by
        nlinarith
      have f2: x * y * z ≤ -6 := by
        nlinarith
      nlinarith

    -- we show that 0 < x
    have lx: 0 < x := by
      linarith

    -- now we can turn them in postive terms
    set a:= -w with ha
    set b:= -z with hb
    replace ha: w = -a := by
      simp [ha]
    replace hb: z = -b := by
      simp [hb]
    simp [ha, hb] at *
    clear hxz ha hb
    clear_value a b

    -- then we have a = 1
    have vb: b = 1 := by
      by_contra! rb
      replace rb: 2 ≤ b := by omega
      have ra: 3 ≤ a := by omega
      have f1: 6 ≤ a * b := by
        nlinarith
      have f2: 6 ≤ a * b * x := by
        nlinarith
      nlinarith

    simp [vb] at *

    -- similarly, we have y = 1
    have vy: y = 1 := by
      by_contra! ry
      replace ry: 2 ≤ y := by omega
      have rx: 3 ≤ x := by omega
      have f1: 6 ≤ x * y := by
        nlinarith
      have f2: 6 ≤ x * y * a := by
        nlinarith
      nlinarith

    simp [vy] at *

    -- then we have x = 2
    have vx: x = 2 := by
      have rx: x < 3 := by nlinarith
      omega
    simp [vx] at h
    replace h: a = 2 := by omega
    simp [h, vx]


/-If four distinct positive integers m,n,p and q satisfy the equation
(7−m)(7−n)(7−p)(7−q)=4,
then the sum m+n+p+q is equal to:
(a) 10 ; (b) 21 ; (c) 24 ; (d) 26 ; (e) 28 .-/

theorem number_theory_253981 {m n p q: ℤ}(hmn: m < n) (hnp: n < p) (hpq: p < q)
(h: (7 - m) * (7 - n) * (7 - p) * (7 - q) = 4):
  m + n + p + q = 28 := by

  -- for convenience, we set 7 - x to y
  rw [show m + n + p + q = 28 - (7 - m) - (7 - n) - (7 - p) - (7 - q) by ring]
  set x:= 7 - m
  set y:= 7 - n
  set z:= 7 - p
  set w:= 7 - q
  replace hmn: y < x := by
    omega
  replace hnp: z < y := by
    omega
  replace hpq: w < z := by
    omega
  clear_value x y z w

  -- use lemma to obtain the result
  have i:= lemma_1 x y z w hmn hnp hpq h
  linarith