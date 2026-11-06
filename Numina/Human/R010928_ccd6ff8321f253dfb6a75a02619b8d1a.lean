import Mathlib

-- we first consider the case when a < -1
lemma lemma_1 (a: ℤ) (ha: a < -1): ∀ N: ℕ, ∃ x y: ℤ, N ≤ |x| ∧
  x ^ 2 + a * x * y + y ^ 2 = 1 := by

    -- we prove a stronger result by induction
    have h: ∀ N: ℕ, ∃ x y: ℤ, 0 < y ∧ y < x ∧ N ≤ x ∧ x ^ 2 + a * x * y + y ^ 2 = 1 := by
      intro N
      induction' N with N ih

      -- base case
      .
        use -a
        use 1
        norm_num
        constructor
        .
          linarith
        .
          constructor
          .
            linarith
          .
            ring

      -- inductive step
      .
        replace ha: a ≤ -2 := by omega
        obtain ⟨x, y, hy, l, h⟩:= ih
        use (-a * x - y)
        use x
        have o1: 0 < x := by
          linarith
        simp [o1]
        have o2: x < -(a * x) - y:= by
          nlinarith
        simp [o2]
        clear o1 o2
        constructor
        .
          nlinarith
        .
          ring_nf
          rcases h with ⟨f, g⟩
          nlinarith

    -- we prove the result by the above stronger result
    intro N
    obtain ⟨x, y, hy, hxy⟩ := h N
    use x
    use y
    rw [show |x| = x by apply abs_of_nonneg; linarith]
    omega


-- use lemma_1 we can tackle the case 1 < a
lemma lemma_2 (a: ℤ) (ha: 1 < a): ∀ N: ℕ, ∃ x y: ℤ, N ≤ |x| ∧
  x ^ 2 + a * x * y + y ^ 2 = 1 := by
    intro N
    set b:= -a
    have hb: b < -1 := by
      simp [b]
      linarith
    rw [show a = -b by simp [b]]
    have i:= lemma_1 b hb N
    obtain ⟨x, y, hx, hxy⟩ := i
    use x
    use -y
    simp [hx]
    nlinarith


-- for the case |a| ≤ 1, we show a stronger result, i.e. it's true even for a: ℝ
lemma lemma_3 (a: ℝ) (h: ∀ N: ℕ, ∃ x y: ℤ, N ≤ |x| ∧
  x ^ 2 + a * x * y + y ^ 2 = 1): a ∈ Set.Iic (-2) ∪ Set.Ici 2 := by

    by_contra! l
    simp at l
    have ra: 0 < 2 - |a| := by
      rcases l with ⟨la1, la2⟩
      by_cases i: 0 ≤ a
      .
        rw [show |a| = a by apply abs_of_nonneg; linarith]
        linarith
      .
        rw [show |a| = -a by apply abs_of_neg; linarith]
        linarith

    -- we give N large enough, prove contradiction by size argument
    set N:= max (⌊1 / (2 - |a|)⌋₊ + 1) 2
    specialize h N
    obtain ⟨x, y, hx, h⟩ := h
    simp [N] at hx
    rcases hx with ⟨l1, l2⟩

    replace h: a * x * y = -(x ^ 2 + y ^ 2 - 1) := by
      linarith
    replace h: |a * x * y| = |-(x ^ 2 + y ^ 2 - (1: ℝ))| := by
      rw [h]
    repeat rw [abs_mul] at h
    have o: 0 ≤ x ^ 2 + y ^ 2 - 1 := by
      by_contra! l
      replace l: x ^ 2 + y ^ 2 = 0 := by
        have r: 0 ≤ x ^ 2 + y ^ 2 := by
          nlinarith
        omega
      have l1: x = 0 := by nlinarith
      have l2: y = 0 := by nlinarith
      simp [l1, l2] at h
    have eq: |-(x ^ 2 + y ^ 2 - (1: ℝ))| = - -(x ^ 2 + y ^ 2 - (1: ℝ)) := by
      rw [abs_eq_neg_self]
      rify at o
      linarith
    rw [eq] at h
    clear o eq
    ring_nf at h
    have h':= h
    set x': ℝ := ↑x
    set y': ℝ := ↑y

    -- h is the key inequality where we find contradiction
    replace h: 2 * |x'| * |y'| - 1 ≤ |a| * |x'| * |y'| := by
      have s: (2: ℝ) * |x'| * |y'| - 1 ≤ x' ^ 2 + y' ^ 2 - 1 := by
        have s1: (0: ℝ) ≤ x' ^ 2 + y' ^ 2 - 2 * |x'| * |y'| := by
          rw [show (x': ℝ) ^ 2 = (|x'|) ^ 2 by simp]
          rw [show (y': ℝ) ^ 2 = (|y'|) ^ 2 by simp]
          have v: |x'| ^ 2 + |y'| ^ 2 - 2 * |x'| * |y'| = (|x'| - |y'|) ^ 2 := by
            ring
          rw [v]
          nlinarith
        nlinarith
      rw [h]
      nlinarith
    replace h: (2 - |a|) * (|x'| * |y'|) ≤ 1 := by nlinarith

    -- we show that y is not zero, then 1 ≤ |y'|
    have p: 1 ≤ |y'| := by
      simp [y']
      norm_cast
      by_contra! e
      have o: 0 ≤ |y| := by
        apply abs_nonneg
      replace o: |y| = 0 := by omega
      simp at o
      simp [o, y'] at h'
      simp [x'] at h'
      replace h': (x - 1) * (x + (1: ℝ)) = 0 := by nlinarith
      simp at h'
      have v: |x| ≤ 1 := by
        rify
        rcases h' with t | t
        .
          replace t: x = (1: ℝ) := by linarith
          simp [t]
        .
          replace t: x = -(1: ℝ) := by linarith
          simp [t]
      linarith

    replace h: (2 - |a|) * |x'| ≤ 1 := by nlinarith
    simp [x'] at h
    rw [← Int.cast_abs] at h
    replace l1: (2 - |a|)⁻¹ < |x| := by
      have s: (2 - |a|)⁻¹ < ↑⌊(2 - |a|)⁻¹⌋₊ + 1 := by
        apply Nat.lt_floor_add_one
      rify at l1
      rw [← Int.cast_abs] at l1
      nlinarith
    rw [Int.cast_abs] at h l1
    set u:= (|x|: ℝ)
    set v:= 2 - |a|
    clear *- ra h l1
    clear_value u v
    field_simp at l1
    have i: (v * u) * (1 / v) < u := by
      have p: 0 < 1 / v := by
        rw [one_div_pos]
        linarith
      nlinarith
    rw [show (v * u) * (1 / v) = u by field_simp] at i
    simp at i


/-Find all integers a such that the equation x ^ 2 + axy + y ^ 2 = 1
has infinitely many integer solutions -/

theorem number_theory_7845: {a: ℤ | ∀ N: ℕ, ∃ x y: ℤ, N ≤ |x| ∧
  x ^ 2 + a * x * y + y ^ 2 = 1} = {a: ℤ | 1 < |a|} := by

  ext a
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rify at h
    set b: ℝ := (a: ℝ)
    have i:= lemma_3 b
    rify at i
    simp only [h] at i
    simp at i
    simp [b] at i
    simp
    rcases i with i | i
    .
      norm_cast at i
      simp at i
      rw [show |a| = -a by apply abs_of_neg; linarith]
      linarith
    .
      norm_cast at i
      rw [show |a| = a by apply abs_of_nonneg; linarith]
      linarith

  -- the backward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rw [lt_abs] at h

    -- we use lemma_1 and lemma_2 to prove the result
    rcases h with h | h
    .
      apply lemma_2
      exact h
    .
      apply lemma_1
      linarith


