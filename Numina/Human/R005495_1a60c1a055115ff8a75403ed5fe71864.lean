import Mathlib

/-Suppose N is a 6-digit number having base-10 representation abcdef,
N is 6/7 of the number having base-10 representation defabc,
find N -/
theorem number_theory_608493(N: ℕ)(a b c d e f: ℕ) (ha1: 1 ≤ a) (ha2: a ≤ 9) (hb1: 0 ≤ b) (hb2: b ≤ 9)
  (hc1: 0 ≤ c) (hc2: c ≤ 9) (hd1: 0 ≤ d) (hd2: d ≤ 9) (he1: 0 ≤ e) (he2: e ≤ 9)
  (hf1: 1 ≤ f) (hf2: f ≤ 9) (hn1: N = 10 ^ 5 * a + 10 ^ 4 * b + 10 ^ 3 * c + 10 ^ 2 * d + 10 * e + f)
  (hn2: (N: ℚ) = (6: ℚ) / 7 * (10 ^ 5 * d + 10 ^ 4 * e + 10 ^ 3 * f + 10 ^ 2 * a + 10 * b + c)): N = 461538 := by
  let x:= 10 ^ 2 * a + 10 * b + c  -- x = abc in base 10 --
  let y:= 10 ^ 2 * d + 10 * e + f  -- y = def in base 10 --
  have bx1: 1 ≤ x := by omega
  have bx2: x ≤ 999 := by omega
  have by1: 1 ≤ y := by omega
  have by2: y ≤ 999 := by omega
  replace hn1: N = 10 ^ 3 * x + y := by
    rw [hn1]
    ring

  -- now we need to turn the rational version of equation hn2 into an integer equation --
  replace hn2: (N: ℚ) = (6: ℚ) / 7 * (10 ^ 3 * y + x) := by
    rw [hn2]
    simp [x,y]
    ring_nf
  replace hn2: 7 * (N: ℚ) = 6 * (10 ^ 3 * y + x) := by
    simp [hn2]
    ring_nf
  rw [show 7 * (N: ℚ) = ↑(7 * N) by simp] at hn2
  have eq: 6 * (10 ^ 3 * (y: ℚ) + (x: ℚ)) = Nat.cast (6 * (10 ^ 3 * y + x)) := by
    simp
    left
    norm_num
  rw [eq] at hn2
  rw [Rat.natCast_inj] at hn2
  rw [hn1] at hn2
  simp at hn2

   -- now we need to show that x = 461, y = 538 --
  have val: x = 461 ∧ y = 538 := by
    clear_value x y
    clear * - bx1 bx2 by1 by2 hn2
    ring_nf at hn2
    have h: 6994 * x = 5993 * y := by
      calc
        6994 * x = 7000 * x - 6 * x := by omega
               _ = x * 7000 + y * 7 - y * 7 - 6 * x := by omega
               _ = x * 6 + y * 6000 - y * 7 - 6 * x := by omega
               _ =5993 * y := by omega
    clear hn2
    -- now divide 13 on both sides --
    replace h: 538 * x = 461 * y := by
      omega
    have dvdx: 461 ∣ x := by
      have dvd1: 461 ∣ 538 * x := by
        rw [h]
        omega
      have cop: Nat.Coprime 461 538 := by
        norm_num
      apply Nat.Coprime.dvd_of_dvd_mul_left cop
      exact dvd1
    apply exists_eq_mul_right_of_dvd at dvdx
    obtain ⟨k, hk⟩ := dvdx
    have bk: k = 1 ∨ k = 2 := by omega
    rcases bk with l | l
    . rw [l] at hk
      simp at hk
      simp [hk] at h
      omega
    . rw [l] at hk
      simp at hk
      simp [hk] at h
      omega

  -- Finally, plug x and y into hn1 --
  simp [val] at hn1
  omega