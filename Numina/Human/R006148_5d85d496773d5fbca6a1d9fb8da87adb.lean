import Mathlib

-- we show a technic lemma for sets with card 3, it's easy intutively, however, troublesome to formalize
lemma lemma_1 (x y z: ℝ) (s1: x ≠ y) (s2: x ≠ z) (s3: y ≠ z):
  ∃ a b c, a < b ∧ b < c ∧ {a, b, c} = ({x, y, z}: Set ℝ) := by

  by_cases l1: x < y
  .
    by_cases l2: y < z
    .
      use x, y, z
    .
      simp at l2
      by_cases l3: x < z
      .
        use x, z, y
        refine ⟨(by linarith), ?_, ?_⟩
        .
          by_contra! o
          replace o: y = z := by linarith
          simp [o] at s3
        .
          ext a
          simp
          tauto
      .
        simp at l3
        use z, x, y
        refine ⟨?_, ?_, ?_⟩
        .
          by_contra! g
          replace g: z = x := by linarith
          tauto
        .
          by_contra! g
          replace g: y = x := by linarith
          tauto
        .
          ext a
          simp
          tauto
  .
    simp at l1
    replace l1: y < x := by
      by_contra! o
      replace o: y = x := by linarith
      tauto
    by_cases r: z < y
    .
      use z, y, x
      simp [r, l1]
      ext a
      simp
      tauto
    .
      simp at r
      replace r: y < z := by
        by_contra! o
        replace o: y = z := by linarith
        tauto
      by_cases s: x < z
      .
        use y, x, z
        simp [l1, s]
        ext a
        simp
        tauto
      .
        simp at s
        replace s: z < x := by
          by_contra! o
          replace o: z = x := by linarith
          tauto
        use y, z, x
        simp [r, s]
        ext a
        simp
        tauto

/- Let $k$ be an integer. If the equation $ ( x - 1 ) | x + 1 | = x + \frac { k } { 2020 } $
has three distinct real roots, how many different possible values of $k$ are there? -/

theorem algebra_623820: {k: ℤ | {x: ℝ | (x - 1) * |x + 1| = x + k / 2020}.encard = 3}.encard = 4544 := by

  -- it suffices to give a bound for k
  suffices {k: ℤ | {x: ℝ | (x - 1) * |x + 1| = x + k / 2020}.encard = 3} = Finset.Icc (-2524) 2019 by
    rw [this]
    rw [Set.encard_coe_eq_coe_finsetCard]
    simp
  ext k
  rw [Set.mem_setOf]
  simp
  have u: -2524 ≤ k ∧ k ≤ 2019 ↔ -2525 < k ∧ k < 2020 := by
    omega
  rw [Set.encard_eq_three]
  constructor

  -- the forward direction
  .
    intro h
    by_contra! l
    obtain ⟨x, y, z, s1, s2, s3, h⟩ := h
    set s:= {x: ℝ | (x - 1) * |x + 1| = x + ↑k / 2020}
    have f:= lemma_1 x y z s1 s2 s3
    obtain ⟨a, b, c, l1, l2, f⟩ := f
    rw [← f] at h
    clear s1 s2 s3 f
    have ha: a ∈ s := by
      simp [h]
    have hb: b ∈ s := by
      simp [h]
    have hc: c ∈ s := by
      simp [h]
    simp [s] at ha hb hc
    clear_value s
    clear h u

    by_cases r: k ≤ -2525

    -- case k ≤ -2525, we show that there are only two solutions
    .
      -- we first show that -1 ≤ b, i.e., b and c are in the branch of P2
      have lb: -1 ≤ b := by
        by_contra! r
        rw [show |a + 1| = -(a + 1) by apply abs_of_nonpos; linarith] at ha
        rw [show |b + 1| = -(b + 1) by apply abs_of_nonpos; linarith] at hb
        clear hc l
        set q:= (k: ℝ) / 2020
        clear_value q
        have u: (a - b) * (a + b + 1) = 0 := by
          clear *- ha hb
          nlinarith
        simp at u
        rcases u with u | v
        .
          replace u: a = b := by linarith
          simp [u] at l1
        .
          clear *- l1 l2 r v
          nlinarith

      clear l
      clear ha l1
      rw [show |b + 1| = b + 1 by apply abs_of_nonneg; linarith] at hb
      rw [show |c + 1| = c + 1 by apply abs_of_nonneg; linarith] at hc
      have i: -2525 ≤ k := by
        rify
        suffices -2525 / 2020 ≤ (k: ℝ) / 2020 by
          clear *- this
          linarith
        replace hb: b ^ 2 - b - 1 = k / 2020 := by
          clear *- hb
          nlinarith
        rw [← hb]
        clear *-
        norm_num
        suffices 0 ≤ b ^ 2 - b + 1 / 4 by linarith
        rw [show b ^ 2 - b + 1 / 4 = (b - 1 / 2) ^ 2 by ring]
        apply sq_nonneg
      replace i: k = -2525 := by linarith
      clear r
      simp [i] at *
      rw [show -(2525: ℝ)/ 2020 = -5 / 4 by norm_num] at *
      replace hb: (b - 1 / 2) ^ 2 = 0 := by
        clear *- hb
        ring_nf
        nlinarith
      replace hc: (c - 1 / 2) ^ 2 = 0 := by
        clear *- hc
        ring_nf
        nlinarith
      simp at hb hc
      linarith

    -- case 2019 < k, there are only two solutions on P2
    .
      simp at r
      replace r: -2524 ≤ k := by omega
      apply l at r
      clear l

      -- we show that -1 ≤ a, i.e. a b c are all on the branch of P2
      have la: -1 ≤ a := by
        by_contra! l
        clear *- ha l r
        set q:= k / (2020: ℝ)
        replace r: 1 ≤ q := by
          simp [q]
          replace r: 2020 ≤ k := by omega
          rify at r
          linarith
        clear_value q
        rw [show |a + 1| = -(a + 1) by apply abs_of_nonpos; linarith] at ha
        nlinarith

      -- then there are three different solutions are the branch of P2, contradiction
      set q:= k / (2020: ℝ)
      rw [show |a + 1| = a + 1 by apply abs_of_nonneg; linarith] at ha
      rw [show |b + 1| = b + 1 by apply abs_of_nonneg; linarith] at hb
      rw [show |c + 1| = c + 1 by apply abs_of_nonneg; linarith] at hc
      clear r la
      clear_value q
      have f1: (a - b) * (a + b - 1) = 0 := by
        clear *- ha hb
        ring_nf
        nlinarith
      have f2: (b - c) * (b + c - 1) = 0 := by
        clear *- hb hc
        ring_nf
        nlinarith
      simp at f1 f2
      clear ha hb hc
      rcases f1 with f | f <;> rcases f2 with g | g <;> linarith


  -- the backward direction
  .
    intro h
    rw [u] at h
    clear u
    rcases h with ⟨h1, h2⟩
    set q:= k / (2020: ℝ)
    replace h1: -5 / 4 < q := by
      simp [q]
      rify at h1
      linarith
    replace h2: q < 1 := by
      simp [q]
      rify at h2
      linarith
    clear_value q
    set x1:= (-1 - √(5 - 4 * q)) / 2
    set x2:= (1 - √(4 * q + 5)) / 2
    set x3:= (1 + √(4 * q + 5)) / 2

    -- we claim that x1 x2 x3 are all solutions
    use x1, x2, x3
    have r1: x1 < -1 := by
      simp [x1]
      have y: 1 < √(5 - 4 * q) := by
        rw [Real.lt_sqrt]
        linarith
        norm_num
      linarith
    have r2: -1 ≤ x2 := by
      simp [x2]
      have y: √(4 * q + 5) ≤ 3 := by
        rw [Real.sqrt_le_left]
        linarith
        norm_num
      linarith
    have r3: -1 ≤ x3 := by
      simp [x3]
      have y: 0 ≤ √(4 * q + 5) := by
        apply Real.sqrt_nonneg
      linarith
    have f1: x1 ≠ x2 := by
      by_contra! o
      clear *- o r1 r2
      linarith
    have f2: x1 ≠ x3 := by
      by_contra! o
      clear *- o r1 r3
      linarith
    have f3: x2 ≠ x3 := by
      by_contra! o
      simp [x2, x3] at o
      clear *- o h1 h2
      replace o: √(4 * q + 5) = 0 := by
        linarith
      rw [Real.sqrt_eq_zero] at o
      linarith
      linarith
    refine ⟨f1, f2, f3, ?_⟩
    clear f1 f2 f3
    ext x
    constructor

    -- one direction, show that any solution x is in the set {x1 x2 x3}
    .
      intro h
      rw [Set.mem_setOf] at h
      simp
      by_cases l: x ≤ -1

      -- case x ≤ -1
      .
        left
        rw [show |x + 1| = -(x + 1) by apply abs_of_nonpos; linarith] at h
        clear_value x2 x3
        simp [x1]
        ring_nf at h
        set y:= -2 * x - 1
        have sy: y ^ 2 = 5 - 4 * q := by
          clear *- h
          simp [y]
          nlinarith
        symm at sy
        rw [← Real.sqrt_eq_iff_eq_sq] at sy
        simp [y] at sy
        clear *- sy
        linarith
        linarith
        simp [y]
        linarith

      -- case -1 < x
      .
        simp at l
        right
        rw [show |x + 1| = (x + 1) by apply abs_of_nonneg; linarith] at h
        simp [x2, x3]
        clear_value x1 x2 x3
        ring_nf at h
        set y:= 2 * x - 1
        have sy: y ^ 2 = 4 * q + 5 := by
          clear *- h
          simp [y]
          nlinarith
        by_cases i: 0 ≤ y
        .
          symm at sy
          rw [← Real.sqrt_eq_iff_eq_sq] at sy
          simp [y] at sy
          right
          clear *- sy
          nlinarith
          linarith
          tauto
        .
          set z:= -y
          rw [show y ^ 2 = z ^ 2 by simp [z]] at sy
          symm at sy
          rw [← Real.sqrt_eq_iff_eq_sq] at sy
          simp [y, z] at sy
          left
          clear *- sy
          nlinarith
          linarith
          simp [z]
          simp at i
          linarith [i]

    -- another direction, verify x1 x2 x3 are indeed solutions
    .
      intro h
      simp at h
      rw [Set.mem_setOf]
      rcases h with h | h | h

      --verify x1
      .
        rw [← h] at r1
        simp [x1] at h
        clear_value x1 x2 x3
        rw [show |x + 1| = - (x + 1) by apply abs_of_nonpos; linarith]
        suffices x ^ 2 + x + q - 1 = 0 by
          clear *- this
          linarith
        simp [h]
        ring_nf
        have i: √(5 - q * 4) ^ 2 = 5 - q * 4 := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          .
            linarith
          .
            apply Real.sqrt_nonneg
        rw [i]
        ring

      -- verify x2
      .
        rw [← h] at r2
        simp [x2] at h
        clear_value x1 x2 x3
        rw [show |x + 1| = (x + 1) by apply abs_of_nonneg; linarith]
        suffices x ^ 2 - x - q - 1 = 0 by
          clear *- this
          linarith
        simp [h]
        ring_nf
        have i: √(5 + q * 4) ^ 2 = 5 + q * 4 := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          .
            linarith
          .
            apply Real.sqrt_nonneg
        rw [i]
        ring

      --verify x3
      .
        rw [← h] at r3
        simp [x3] at h
        clear_value x1 x2 x3
        rw [show |x + 1| = (x + 1) by apply abs_of_nonneg; linarith]
        suffices x ^ 2 - x - q - 1 = 0 by
          clear *- this
          linarith
        simp [h]
        ring_nf
        have i: √(5 + q * 4) ^ 2 = 5 + q * 4 := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          .
            linarith
          .
            apply Real.sqrt_nonneg
        rw [i]
        ring