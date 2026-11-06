import Mathlib

-- we write the simp form of vieta's formula as a lemma
lemma vieta_formula {p q x1 x2: ℝ} (ne: x1 ≠ x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p ∧ x1 * x2 = q := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  constructor
  .
    linarith
  .
    have f: (x1 + x2) ^ 2 - 2 * (x1 * x2) + p * (x1 + x2) + 2 * q = 0 := by
      nlinarith
    replace h: x1 + x2 = -p := by linarith
    simp [h] at f
    nlinarith

/-Given that the two roots of the quadratic equation
x^2 +mx+2520=0 are positive integers,
find the maximum possible value of m -/

theorem algebra_628897: IsGreatest {m: ℝ | ∃ a b: ℤ, 0 < a ∧ 0 < b ∧
  a ^ 2 + m * a + 2520 = 0 ∧ b ^ 2 + m * b + 2520 = 0 ∧ ∀ y: ℝ, y ^ 2 + m * y + 2520 = 0 → y = a ∨ y = b} (-101) := by

    constructor

    -- the forward direction
    .
      simp
      use 45
      norm_num
      use 56
      norm_num
      intro y h
      rw [show y ^ 2 + -(101 * y) + 2520 = (y - 45) * (y - 56) by ring] at h
      simp at h
      rcases h with h | h
      .
        left
        linarith
      .
        right
        linarith

    -- the backward direction
    .
      intro m h
      simp only [Set.mem_setOf_eq] at h
      obtain ⟨a, b, la, lb, ha, hb, hy⟩ := h
      by_cases l: a = b

      -- case1, multiple roots
      .
        simp [← l] at hy
        clear hb l lb
        set c:= -m - a -- we show that c is also a root
        specialize hy c
        have o: c ^ 2 + m * c + 2520 = 0 := by
          simp [c]
          nlinarith
        simp [o] at hy -- hence c = a
        simp [c] at hy
        replace hy: m = -2 * a := by nlinarith
        simp [hy] at ha
        ring_nf at ha
        norm_cast at ha
        have la1: 50 < a := by nlinarith
        have la2: a < 51 := by nlinarith
        omega

      -- case2, distinct roots
      .
        clear hy
        replace l: (a: ℝ) ≠ b := by
          by_contra! i
          simp at i
          simp [i] at l

        -- then we apply vieta's formula
        have f:= vieta_formula l ha hb
        rcases f with ⟨f, g⟩
        norm_cast at g
        have d: a ∣ 2520 := by
          rw [← g]
          simp

        -- for convenience, prove by contradction
        by_contra! i
        replace i: -m < 101 := by linarith
        rw [← f] at i
        clear f ha hb
        norm_cast at i
        by_cases r: a < b
        
        -- case a < b
        .
          have ra: a < 51 := by nlinarith
          have rb: b < 100 := by nlinarith
          replace la: 25 < a := by nlinarith

          -- then we check all value of a
          interval_cases a
          all_goals norm_num at d
          all_goals omega

        -- case a > b
        .
          simp at l
          replace r: b < a := by omega
          clear l
          have ra: a < 100 := by nlinarith
          have rb: b < 51 := by nlinarith
          replace lb: 25 < b := by nlinarith

          -- then we check all value of b
          interval_cases b
          all_goals norm_num at d
          all_goals omega