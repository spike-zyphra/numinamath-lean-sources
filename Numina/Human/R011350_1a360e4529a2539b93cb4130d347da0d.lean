import Mathlib

open Real

-- we first show that log is injective on (0, +∞)
lemma log_inj (x y: ℝ) (hx: 0 < x) (hy: 0 < y):
  log x = log y ↔ x = y := by
    constructor
    .
      intro h
      have l1: log x ≤ log y := by
        rw [h]
      rw [Real.log_le_log_iff] at l1
      have l2: log y ≤ log x := by
        rw [h]
      rw [Real.log_le_log_iff] at l2
      all_goals linarith
    .
      intro h
      simp [h]

-- take out the log
lemma lemma_1 (a x: ℝ) (h1: 0 < x - 1) (h2: 0 < 3 - x) (h3: 0 < a - x):
  log (x - 1) + log (3 - x) = log (a - x) ↔ a = - x ^ 2 + 5 * x - 3 := by

    rw [← Real.log_mul]
    rw [log_inj]
    ring_nf
    constructor

    -- the forward direction
    .
      intro h
      nlinarith

    -- the backward direction
    .
      intro h
      nlinarith

    nlinarith
    linarith
    by_contra! o
    simp [o] at h1
    by_contra! o
    simp [o] at h2

/-If the equation
lg(x−1)+lg(3−x)=lg(a−x)
has only one real root with respect to x,
find the range of real number a.-/

theorem algebra_281276: {a: ℝ | ∃! x, 0 < x - 1 ∧ 0 < 3 - x ∧
  0 < a - x ∧ log (x - 1) + log (3 - x) = log (a - x)} = Set.Ioc 1 3 ∪ {13 / 4} := by

  ext a
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    obtain ⟨x, hx, h⟩ := h
    simp

    -- use lemma_1 to take out the log
    rcases hx with ⟨lx1, lx2, lx3, hx⟩
    rw [lemma_1 a x (by linarith) (by linarith) (by linarith)] at hx
    clear lx3  -- it's implied by the other three
    have l1: 1 < a := by
      rw [hx]
      nlinarith
    have l2: a ≤ 13 / 4 := by
      rw [hx]
      have o: 0 ≤ x ^ 2 - 5 * x + 3 + 13 / 4 := by
        rw [show x ^ 2 - 5 * x + 3 + 13 / 4 = (x - 5 / 2) ^ 2 by ring]
        nlinarith
      linarith
    simp [l1]
    by_contra! l
    rcases l with ⟨u, v⟩
    replace l1: 3 < a := by
      linarith
    clear v
    replace l2: a < 13 / 4 := by
      by_contra! o
      replace o: a = 13 / 4 := by
        linarith
      simp [o] at u
    clear u

    -- then we show that there are two solutions for x
    replace hx: (x - 5 / 2) ^ 2 = 13 / 4 - a := by nlinarith

    -- we list the two solutions
    set x1:= 5 / 2 + sqrt (13 / 4 - a)
    set x2:= 5 / 2 - sqrt (13 / 4 - a)

    have h1:= h x1
    simp at h1
    have f1: 1 < x1 := by
      simp [x1]
      have o: 0 ≤ √(13 / 4 - a) := by
        apply sqrt_nonneg
      nlinarith
    have g1: x1 < 3 := by
      simp [x1]
      have o: √(13 / 4 - a) < 1 / 2 := by
        rw [sqrt_lt]
        nlinarith
        linarith
        norm_num
      linarith
    have s1: x1 < a := by
      simp [x1]
      have o: √(13 / 4 - a) < a - 5 / 2 := by
        rw [sqrt_lt]
        nlinarith
        linarith
        norm_num
        linarith
      linarith
    simp [f1, g1, s1] at h1
    have e1: a = - x1 ^ 2 + 5 * x1 - 3 := by
      have o: (x1 - 5 / 2) ^ 2 = 13 / 4 - a := by
        simp [x1]
        have o: √(13 / 4 - a) ^ 2 = 13 / 4 - a := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply sqrt_nonneg
        linarith
      clear_value x1
      nlinarith
    rw [lemma_1 a x1 (by linarith) (by linarith) (by linarith)] at h1
    apply h1 at e1  -- we get x1 = y

    -- similarly, we show that x2 is also a solution
    clear f1 g1 s1 h1
    have h2:= h x2
    simp at h2
    have f2: 1 < x2 := by
      simp [x2]
      have o: √(13 / 4 - a) < 1 / 2 := by
        rw [sqrt_lt]
        nlinarith
        linarith
        norm_num
      nlinarith
    have g2: x2 < 3 := by
      simp [x2]
      have o: 0 ≤ √(13 / 4 - a) := by
        apply sqrt_nonneg
      linarith
    have s2: x2 < a := by
      simp [x2]
      have o: 0 ≤ √(13 / 4 - a) := by
        apply sqrt_nonneg
      nlinarith
    simp [f2, g2, s2] at h2
    have e2: a = - x2 ^ 2 + 5 * x2 - 3 := by
      have o: (x2 - 5 / 2) ^ 2 = 13 / 4 - a := by
        simp [x2]
        have o: √(13 / 4 - a) ^ 2 = 13 / 4 - a := by
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply sqrt_nonneg
        linarith
      clear_value x2
      nlinarith
    rw [lemma_1 a x2 (by linarith) (by linarith) (by linarith)] at h2
    apply h2 at e2  -- we get x2 = y

    --then we have x1 = x2, which is a contradiction
    rw [← e2] at e1
    simp [x1, x2] at e1
    replace e1: √(13 / 4 - a) = 0 := by
      linarith
    rw [Real.sqrt_eq_zero] at e1
    linarith
    linarith


  -- the backward direction
  .
    intro h
    simp
    simp at h
    rcases h with h | h

    -- case 1: a = 13 / 4
    .
      use 5 / 2
      constructor
      .
        simp
        rw [lemma_1]
        norm_num
        simp [h]
        norm_num
        norm_num
        norm_num
        simp [h]
        norm_num
      .
        intro y l
        rw [lemma_1 a y (by linarith) (by linarith) (by linarith)] at l
        rcases l with ⟨l1, l2, l3, l⟩
        clear l3
        simp [h] at l
        nlinarith

    -- case 2: a ∈ Ioc 1 3
    .
      rcases h with ⟨l1, l2⟩

      -- we directly compute the unique solution
      set x2:= 5 / 2 - sqrt (13 / 4 - a)
      use x2
      simp
      have f2: 1 < x2 := by
        simp [x2]
        have o: √(13 / 4 - a) < 3 / 2 := by
          rw [sqrt_lt]
          nlinarith
          linarith
          norm_num
        nlinarith
      have g2: x2 < 3 := by
        simp [x2]
        have o: 0 ≤ √(13 / 4 - a) := by
          apply sqrt_nonneg
        linarith
      have s2: x2 < a := by
        simp [x2]
        by_cases f: a = 3
        .
          have o: 0 ≤ √(13 / 4 - 3) := by
            apply sqrt_nonneg
          rw [f]
          linarith
        .
          replace l2: a < 3 := by
            by_contra! o
            replace o: a = 3 := by
              linarith
            simp [o] at f
          have o: 5 / 2 - a < √(13 / 4 - a) := by
            by_cases g: a ≤ 5 / 2
            .
              rw [lt_sqrt]
              have o: 0 < - (a - 5 / 2) ^ 2 + (13 / 4 - a) := by
                ring_nf
                nlinarith
              linarith
              linarith
            .
              simp at g
              have o: 0 ≤ √(13 / 4 - a) := by
                apply sqrt_nonneg
              linarith
          nlinarith

      simp [f2, g2, s2]
      have e2: a = - x2 ^ 2 + 5 * x2 - 3 := by
        have o: (x2 - 5 / 2) ^ 2 = 13 / 4 - a := by
          simp [x2]
          have o: √(13 / 4 - a) ^ 2 = 13 / 4 - a := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            linarith
            apply sqrt_nonneg
          linarith
        clear_value x2
        nlinarith
      rw [lemma_1 a x2 (by linarith) (by linarith) (by linarith)]
      simp [e2]
      intro y ly1 ly2 ly3 ly4
      rw [← e2] at ly3 ly4
      rw [lemma_1 a y (by linarith) (by linarith) (by linarith)] at ly4
      rw [e2] at ly4
      replace ly4: -(-x2 ^ 2 + 5 * x2 - 3) + -y ^ 2 + 5 * y - 3 = 0 := by rw [ly4]; ring
      rw [show -(-x2 ^ 2 + 5 * x2 - 3) + -y ^ 2 + 5 * y - 3 = (x2 - y) * (x2 + y - 5)  by ring] at ly4
      simp at ly4
      rcases ly4 with f | f
      .
        linarith
      .
        simp [x2] at f
        replace f: y = 5 / 2 + √(13 / 4 - a) := by
          linarith
        absurd ly2
        simp [f]
        have o: 1 / 2 ≤ √(13 / 4 - a) := by
          rw [show 1 / 2 = √(1 / 4) by symm; rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]; ring; norm_num]
          rw [Real.sqrt_le_sqrt_iff]
          linarith
          linarith
        linarith