import Mathlib

lemma AM_GM_3 (a b c: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b) (hc: 0 ≤ c):
  (a + b + c) ^ 3 ≥ 27 * (a * b * c) := by

    -- we prove by factorization, so we replace a b c by x ^ 3 y ^ 3 z ^ 3 first
      let x:= a ^ (1 / (3: ℝ))
      have hx: x ^ 3 = a := by
          have o: x ^ 3 = x ^ (3: ℝ) := by
            norm_cast
          rw [o]
          simp [x]
          rw [← Real.rpow_mul]
          simp
          exact ha
      have lx: 0 ≤ x := by
        simp [x]
        apply Real.rpow_nonneg
        exact ha
      let y:= b ^ (1 / (3: ℝ))
      have hy: y ^ 3 = b := by
          have o: y ^ 3 = y ^ (3: ℝ) := by
            norm_cast
          rw [o]
          simp [y]
          rw [← Real.rpow_mul]
          simp
          exact hb
      have ly: 0 ≤ y := by
        simp [y]
        apply Real.rpow_nonneg
        exact hb
      let z:= c ^ (1 / (3: ℝ))
      have hz: z ^ 3 = c := by
          have o: z ^ 3 = z ^ (3: ℝ) := by
            norm_cast
          rw [o]
          simp [z]
          rw [← Real.rpow_mul]
          simp
          exact hc
      have lz: 0 ≤ z := by
        simp [z]
        apply Real.rpow_nonneg
        exact hc
      rw [← hx, ← hy, ← hz]
      clear_value x y z
      clear * - lx ly lz

      -- then we do on x y z
      rw [show 27 * (x ^ 3 * y ^ 3 * z ^ 3) = (3 * x * y * z) ^ 3 by ring]
      simp
      rw [pow_le_pow_iff_left₀]
      .
        have v: 0 ≤ x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z := by

          -- show that key factorization
          rw [show x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z =
          (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) by ring]
          apply mul_nonneg
          .
            linarith
          .
            rw [show x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x = ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 2 by ring]
            nlinarith
        nlinarith
      .
        apply mul_nonneg
        apply mul_nonneg
        nlinarith
        nlinarith
        nlinarith
      .
        have s1: 0 ≤ x ^ 3 := by
          rw [show x ^ 3 = x ^ 2 * x by ring]
          nlinarith
        have s2: 0 ≤ y ^ 3 := by
          rw [show y ^ 3 = y ^ 2 * y by ring]
          nlinarith
        have s3: 0 ≤ z ^ 3 := by
          rw [show z ^ 3 = z ^ 2 * z by ring]
          nlinarith
        nlinarith
      .
        norm_num


/-Determine all triples (x;y;z) of integers
x;y;z that satisfy the equation:
xy / z + yz / x + xz / y = 3-/

theorem algebra_159468: {(x, y, z): ℤ × ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
  (x * y) / (z: ℝ) + (y * z) / (x: ℝ) + (x * z) / (y: ℝ) = 3} = {(1, 1, 1), (1, -1, -1), (-1, -1, 1), (-1, 1, -1)} := by

  ext ⟨x, y, z⟩
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    rcases h with ⟨nx, ny, nz, h⟩
    field_simp at h
    replace h: x * y * z = (((x: ℝ) * y) ^ 2 + (y * z) ^ 2 + (x * z) ^ 2) / 3 := by
      nlinarith

    -- we show that 1 ≤ xyz first
    have l1: 0 ≤ x * y * z := by
      rify
      rw [h]
      nlinarith
    replace l1: 1 ≤ x * y * z := by
      by_contra! o
      replace o: x * y * z = 0 := by omega
      simp at o
      omega

    -- then we show that xyz ≤ 1 using AM-GM
    have l2: x * y * z ≤ 1 := by
      have l:= AM_GM_3 (((x: ℝ) * y) ^ 2) ((y * z) ^ 2) ((x * z) ^ 2) (by nlinarith) (by nlinarith) (by nlinarith)
      replace h: ((x: ℝ) * y) ^ 2 + (y * z) ^ 2 + (x * z) ^ 2 = 3 * (x * y * z) := by nlinarith
      replace h: (((x: ℝ) * y) ^ 2 + (y * z) ^ 2 + (x * z) ^ 2) ^ 3 = 27 * ((x * y * z)) ^ 3 := by
        rw [h]
        ring
      rw [h] at l
      clear h
      rw [show ((x: ℝ)* ↑y) ^ 2 * (↑y * ↑z) ^ 2 * (↑x * ↑z) ^ 2 = ((x: ℝ) * y * z) ^ 4 by ring] at l
      rify at l1
      set p:= x * y * (z: ℝ)
      replace l: p ^ 4 ≤ p ^ 3 := by nlinarith
      replace l: p ≤ 1 := by
        rw [show p ^ 4 = p ^ 3 * p by ring] at l
        have o: 0 ≤ p ^ 3 := by
          rw [show p ^ 3 = (p ^ 2) * p by ring]
          nlinarith
        rw [mul_le_iff_le_one_right] at l
        exact l
        by_contra! s
        have c: p ^ 3 = 0 := by linarith
        simp at c
        simp [c] at l1
        norm_num at l1
      have o: p = 1 := by linarith
      simp [p] at o
      rify
      rw [o]

    -- hence xyz = 1
    have o: x * y * z = 1 := by
      linarith
    clear l1 l2 h
    simp
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at o
    rcases o with o | o
    .
      rcases o with ⟨f, g⟩
      rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at f
      rcases f with f | f
      .
        omega
      .
        omega
    .
      rcases o with ⟨f, g⟩
      rw [Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at f
      rcases f with f | f
      .
        omega
      .
        omega


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h | h
    all_goals simp [h]; norm_num