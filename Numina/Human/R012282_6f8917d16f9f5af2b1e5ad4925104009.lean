import Mathlib

open Real

lemma lemma_1 {x: ℝ}: sin x = 0 ∧ cos x = 1 ∨ sin x = 1 ∧ cos x = 0 ↔
    ∃ n: ℤ, x = 2 * n * π ∨ x = 2 * n * π + π / 2 := by

  constructor
  -- the first direction
  .
    intro h
    rcases h with h | h
    .
      rcases h with ⟨h1, h2⟩
      rw [Real.cos_eq_one_iff] at h2
      obtain ⟨l, hl⟩ := h2
      use l
      left
      rw [← hl]
      ring
    .
      rcases h with ⟨h1, h2⟩
      rw [Real.sin_eq_one_iff] at h1
      obtain ⟨l, hl⟩ := h1
      use l
      right
      rw [← hl]
      ring

  -- the second direction
  .
    intro h
    obtain ⟨n, h⟩ := h
    rcases h with h | h
    .
      left
      have o: cos x = 1 := by
        rw [Real.cos_eq_one_iff]
        use n
        rw [h]
        ring
      simp [o]
      have i:= Real.sin_sq_add_cos_sq x
      simp [o] at i
      exact i
    .
      right
      have o: sin x = 1 := by
        rw [Real.sin_eq_one_iff]
        use n
        rw [h]
        ring
      simp [o]
      have i:= Real.sin_sq_add_cos_sq x
      simp [o] at i
      exact i

-- we first prove the case "1" rather than "-1"
lemma lemma_2 (x: ℝ): sin x ^ 3 + cos x ^ 3 = 1 ↔ ∃ n: ℤ, x = 2 * n * π ∨ x = 2 * n * π + π / 2 := by

  -- use lemma_1 to simplify the right side
  rw [← lemma_1]
  constructor

  -- the first direction
  .
    intro h
    rw [← Real.sin_sq_add_cos_sq x] at h

    -- then we factorize h
    replace h: sin x ^ 2 * (sin x - 1) = cos x ^ 2 * (1 - cos x) := by
      nlinarith

    -- for convenience, prove by contradiction
    by_contra! l
    rcases l with ⟨l1, l2⟩
    by_cases s: sin x = 1

    -- case sin x = 1
    .
      simp [s] at l2
      simp [s] at h
      simp [l2] at h
      replace h: cos x = 1 := by linarith
      have i:= Real.sin_sq_add_cos_sq x
      simp [s, h] at i

    -- case sin x ≠ 1
    .
      have ls:= Real.sin_le_one x
      have lc:= Real.cos_le_one x
      replace s: sin x < 1 := by
        by_contra! o
        replace o: sin x = 1 := by
          linarith
        simp [o] at s
      by_cases c: sin x = 0
      -- case sin x = 0
      .
        simp [c] at l1
        simp [c] at h
        replace l1: ¬ 1 - cos x = 0 := by
          by_contra! o
          replace o: cos x = 1 := by
            linarith
          simp [o] at l1
        simp [l1] at h
        have i:= Real.sin_sq_add_cos_sq x
        simp [c, h] at i
      -- case sin x ≠ 0
      .
        clear l1 ls

        -- note that left side of h is negative, while right side is positive
        have u: sin x ^ 2 * (sin x - 1) < 0 := by
          have o: 0 < sin x ^ 2 := by
            have v: 0 ≤ sin x ^ 2 := by
              apply sq_nonneg
            by_contra! o
            replace o: sin x ^ 2 = 0 := by
              linarith
            simp at o
            simp [o] at c
          nlinarith
        rw [h] at u
        absurd u
        simp
        nlinarith


  -- the second direction
  .
    intro h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]

-- then we use lemma_2 to prove the case "-1"
lemma lemma_3 (x: ℝ): sin x ^ 3 + cos x ^ 3 = -1 ↔ ∃ n: ℤ, x = (2 * n + 1) * π ∨ x = (2 * n + 1) * π + π / 2 := by

  constructor

  -- the first direction
  .
    intro h
    set y:= x - π with hy
    have f: sin y ^ 3 + cos y ^ 3 = 1 := by
      rw [hy]
      rw [Real.sin_sub_pi]
      rw [Real.cos_sub_pi]
      nlinarith
    rw [lemma_2] at f
    obtain ⟨n, g⟩ := f
    use n
    rcases g with g | g
    .
      left
      simp [y] at g
      nlinarith
    .
      right
      simp [y] at g
      nlinarith

  -- the second direction
  .
    intro h
    set y:= x - π with hy
    obtain ⟨n, h⟩ := h
    have f: sin y ^ 3 + cos y ^ 3 = 1 := by
      rw [lemma_2]
      rcases h with h | h
      .
        use n
        left
        nlinarith
      .
        use n
        right
        nlinarith
    rw [hy] at f
    rw [Real.sin_sub_pi] at f
    rw [Real.cos_sub_pi] at f
    nlinarith


/- Consider the equation
sin^3 (x)+ cos^3 (x) = -1
How many solutions does it have on the interval [0;6π]?-/

theorem algebra_146095: {x: ℝ | x ∈ Set.Icc 0 (6 * π) ∧ sin x ^ 3 + cos x ^ 3 = -1}.encard = 6 := by
  have t1:= Real.pi_lt_d2
  have t2:= Real.pi_gt_d2

  -- we directly compute the set
  have h_eq: {x: ℝ | x ∈ Set.Icc 0 (6 * π) ∧ sin x ^ 3 + cos x ^ 3 = -1}
    = {π, 3 * π / 2, 3 * π, 7 * π / 2, 5 * π, 11 * π / 2} := by

    ext x
    constructor

    -- the first direction
    .
      intro h
      simp at h
      rcases h with ⟨l, h⟩
      rw [lemma_3] at h
      obtain ⟨n, h⟩ := h
      rcases h with h | h

      -- check two cases separately
      -- first case
      .
        rcases l with ⟨l, r⟩
        simp
        simp [h] at l r
        have ln: -1 ≤ n := by
          rify
          nlinarith
        have rn: n < 3 := by
          rify
          nlinarith
        interval_cases n
        .
          norm_num at l
          linarith
        .
          simp at h
          simp [h]
        .
          simp at h
          norm_num at h
          simp [h]
        .
          simp at h
          norm_num at h
          simp [h]
      -- second case
      .
        rcases l with ⟨l, r⟩
        simp
        simp [h] at l r
        have ln: -1 < n := by
          rify
          nlinarith
        have rn: n < 3 := by
          rify
          nlinarith
        interval_cases n
        .
          simp at h
          replace h: x = 3 * π / 2 := by
            linarith
          simp [h]
        .
          simp at h
          replace h: x = 7 * π / 2 := by
            linarith
          simp [h]
        .
          simp at h
          replace h: x = 11 * π / 2 := by
            linarith
          simp [h]


    -- the second direction
    .
      intro h
      simp at h
      simp
      constructor
      .
        rcases h with h | h | h | h | h | h
        all_goals {
          simp [h]
          constructor
          nlinarith
          nlinarith
        }
      .
        rw [lemma_3]
        rcases h with h | h | h | h | h | h
        all_goals rw [h]
        .
          use 0
          left
          norm_num
        .
          use 0
          right
          ring
        .
          use 1
          left
          norm_num
        .
          use 1
          right
          ring
        .
          use 2
          left
          norm_num
        .
          use 2
          right
          ring


  -- finally we can count the card
  rw [h_eq]
  clear h_eq
  repeat rw [Set.encard_insert_of_not_mem]

  -- for the rest, we need to check that the elements are distinct
  norm_num
  simp
  linarith
  simp
  constructor
  . linarith
  . linarith
  simp
  constructor
  . linarith
  . constructor
    . linarith
    . linarith
  simp
  constructor
  . linarith
  . constructor
    . linarith
    . constructor
      . linarith
      . linarith
  simp
  constructor
  . linarith
  . constructor
    . linarith
    . constructor
      . linarith
      . constructor
        . linarith
        . linarith