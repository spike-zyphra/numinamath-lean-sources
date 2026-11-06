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

-- then we show vieta_formula as a lemma
lemma vieta_formula (p q x1 x2: ℝ) (ne: ¬x1 = x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  linarith


/- In the Cartesian coordinate system, the graph of the function $y=\frac{x+1}{|x|+1}$ has three distinct points lying on the line $l$,
and the sum of the x-coordinates of these three points is $0$. Find the range of the slope of $l$. -/

theorem algebra_624393 {k b : ℝ} (s: Set ℝ) (hk: k ≠ 0) (hs: s = {x: ℝ | k * x + b = (x + 1) / (|x| + 1)})
  (h1: s.encard = 3) (h2: ∑ᶠ x ∈ s, x = 0): 0 < k ∧ k < 2 / 9 := by

  -- we first take out the three distinct solutions from the set s
  rw [Set.encard_eq_three] at h1
  obtain ⟨x, y, z, n1, n2, n3, h1⟩ := h1
  have h0:= lemma_1 x y z n1 n2 n3
  obtain ⟨p, q, r, l1, l2, h0⟩ := h0
  rw [← h0] at h1
  clear h0 n1 n2 n3
  have hp: p ∈ s := by
    simp [h1]
  have hq: q ∈ s := by
    simp [h1]
  have hr: r ∈ s := by
    simp [h1]
  rw [hs] at hp hq hr
  rw [Set.mem_setOf] at hp hq hr
  rw [h1] at h2
  have h3: ∑ᶠ (x : ℝ) (_ : x ∈ ({p, q, r}: Set ℝ)), x = p + q + r := by
    clear *- l1 l2
    repeat rw [finsum_mem_insert]
    simp
    ring
    simp
    linarith
    simp
    simp
    refine ⟨(by linarith), (by linarith)⟩
    simp
  rw [h3] at h2
  clear hs h1 h3

  -- then we show that q must nonpositive
  have lq: q ≤ 0 := by
    by_contra! l
    rw [show |q| = q by apply abs_of_nonneg; linarith] at hq
    rw [show |r| = r by apply abs_of_nonneg; linarith] at hr
    rw [show (q + 1) / (q + 1) = 1 by field_simp] at hq
    have sr: r + 1 ≠ 0 := by
      by_contra! g
      linarith
    rw [show (r + 1) / (r + 1) = 1 by field_simp] at hr
    suffices q = r by
      simp [this] at l2
    clear *- hq hr hk
    rw [← hq] at hr
    suffices k * r - k * q = 0 by
      rw [show k * r - k * q = k * (r - q) by ring] at this
      simp at this
      simp [hk] at this
      linarith
    linarith

  rw [show |q| = -q by apply abs_of_nonpos; linarith] at hq
  rw [show |p| = -p by apply abs_of_nonpos; linarith] at hp

  -- for r, we have 0 ≤ r
  have lr: 0 ≤ r := by
    clear *- l1 l2 lq h2
    linarith
  rw [show |r| = r by apply abs_of_nonneg; linarith] at hr
  rw [show (r + 1) / (r + 1) = 1 by field_simp] at hr
  have f1: -p + 1 ≠ 0 := by
    by_contra! o
    clear *- o l1 l2 lq
    linarith
  have f2: -q + 1 ≠ 0 := by
    by_contra! o
    clear *- o l1 l2 lq
    linarith
  field_simp at hp hq
  replace hp: p ^ 2 + (b + 1 - k) / k * p + (1 - b) / k = 0 := by
    clear *- hp hk
    field_simp
    nlinarith
  replace hq: q ^ 2 + (b + 1 - k) / k * q + (1 - b) / k = 0 := by
    clear *- hq hk
    field_simp
    nlinarith
  clear f1 f2

  -- then we can apply vieta lemma
  have v:= vieta_formula ((b + 1 - k) / k) ((1 - b) / k) p q (by linarith) hp hq
  have hr2: r = (1 - b) / k := by
    clear *- hr hk
    field_simp
    linarith
  simp [hr2, v] at h2
  field_simp at h2

  -- then we obtain the key equality
  replace h2: k = 2 * b := by
    clear *- h2
    linarith
  rw [h2]
  rw [h2] at hr2 hr
  have r0: 0 ≤ b := by
    clear *- hr lr
    nlinarith
  have r1: b ≤ 1 := by
    clear *- hr lr
    nlinarith
  clear hr

  -- first give a simp bound for b
  replace r0: 0 < b := by
    clear *- r0 hk h2
    suffices b ≠ 0 by
      by_contra! o
      replace o: b = 0 := by linarith
      simp [o] at this
    by_contra! o
    simp [o] at h2
    tauto
  replace r1: b < 1 := by
    clear *- r0 r1 hk h2 hq hr2 l2
    suffices b ≠ 1 by
      by_contra! o
      replace o: b = 1 := by linarith
      simp [o] at this
    by_contra! o
    simp [o] at h2
    simp [o, h2] at *
    ring_nf at hq
    simp at hq
    simp [hq, hr2] at l2
  simp [h2] at hp hq
  refine ⟨(by clear *- r0; linarith),?_⟩

  -- then use 0 < Δ to give the precise bound
  have r2: b ≤ 1 / 9 := by
    clear *- hp r0 r1
    have u: p ^ 2 + (b + 1 - 2 * b) / (2 * b) * p + (1 - b) / (2 * b) =
      (p + (1 - b) / (4 * b)) ^ 2 - ((1 - b) ^ 2 / (16 * b ^ 2) - (1 - b) / (2 * b)) := by
        field_simp
        ring
    rw [hp] at u
    clear hp
    set i:= p + (1 - b) / (4 * b)
    clear_value i
    replace u: i ^ 2 = ((1 - b) ^ 2 / (16 * b ^ 2) - (1 - b) / (2 * b)) := by
      set j:= ((1 - b) ^ 2 / (16 * b ^ 2) - (1 - b) / (2 * b))
      clear_value j
      linarith
    have f: (1 - b) ^ 2 / (16 * b ^ 2) - (1 - b) / (2 * b) = (1 - b) * (1 - 9 * b) / (16 * b ^ 2) := by
      field_simp
      ring
    rw [f] at u
    clear f
    have j:= sq_nonneg i
    rw [u] at j
    clear u
    rw [div_nonneg_iff] at j
    rcases j with j | j
    .
      rcases j with ⟨f, g⟩
      clear g
      nlinarith
    .
      rcases j with ⟨f, g⟩
      clear f
      absurd g
      simp
      nlinarith

  -- finally, we only need to show that b ≠ 1 / 9
  suffices b ≠ 1 / 9 by
    clear *- r2 this
    by_contra! o
    replace o: b = 1 / 9 := by linarith
    tauto
  by_contra! o
  simp [o] at h2
  simp [o, h2] at hp hq
  norm_num at hp hq
  clear *- hp hq l1
  rw [show p ^ 2 + 4 * p + 4 = (p + 2) ^ 2 by ring] at hp
  simp at hp
  rw [show q ^ 2 + 4 * q + 4 = (q + 2) ^ 2 by ring] at hq
  simp at hq
  linarith