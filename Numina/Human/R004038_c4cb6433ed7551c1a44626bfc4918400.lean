import Mathlib

open Finset

-- we write a lemma to count the card of the key sets
lemma lemma_1 (p q a: ℝ) (h3: 0 < a):
  {n: ℤ | p < a * n ∧ a * n < q} = Icc (⌊p / a⌋ + 1) (⌈q / a⌉ - 1) := by
    ext n
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨l, r⟩
      replace l: p / a < n := by
        clear *- l h3
        rw [div_lt_iff₀]
        linarith
        tauto
      replace r: n < q / a := by
        rw [lt_div_iff₀']
        linarith
        tauto
      set x:= p / a
      set y:= q / a
      clear_value x y
      refine ⟨?_, ?_⟩
      .
        rw [← Int.floor_le_sub_one_iff] at l
        linarith
      .
        rw [← Int.add_one_le_ceil_iff] at r
        linarith

    -- the backward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨l, r⟩
      replace l: ⌊p / a⌋ ≤ n - 1 := by
        linarith
      rw [Int.floor_le_sub_one_iff] at l
      replace r: n + 1 ≤ ⌈q / a⌉ := by
        linarith
      rw [Int.add_one_le_ceil_iff] at r
      refine ⟨?_, ?_⟩
      .
        rw [div_lt_iff₀] at l
        linarith
        tauto
      .
        rw [lt_div_iff₀'] at r
        linarith
        tauto

-- count the card of finset.icc
lemma lemma_2 (a b: ℤ): (Icc a b).card = max (b - a + 1) 0 := by
  rw [Int.card_Icc]
  simp
  omega

/- Let $a>0$ be a real number for which there exist exactly three natural numbers $n$ such that $1 < an < 2$.
How many natural numbers $m$ can there be, for which $2 < am < 3$? -/

theorem number_theory_232643: {k: ℕ | ∃ a: ℝ, 0 < a ∧ {n : ℤ | 1 < a * n ∧ a * n < 2}.encard = 3
  ∧ k = {m : ℤ | 2 < a * m ∧ a * m < 3}.encard} = {2, 3, 4} := by

  ext k
  constructor

  -- the forward direction: show that only 2 m's and 3 m's and 4 m's are possible
  .
    intro h
    rw [Set.mem_setOf] at h
    obtain ⟨a, ha, h1, h2⟩ := h
    simp
    suffices {m: ℤ | 2 < a * ↑m ∧ a * ↑m < 3}.encard = 2 ∨ {m: ℤ | 2 < a * ↑m ∧ a * ↑m < 3}.encard = 3 ∨
      {m: ℤ | 2 < a * ↑m ∧ a * ↑m < 3}.encard = 4 by
      rw [← h2] at this
      clear *- this
      rcases this with h | h
      .
        norm_cast at h
        tauto
      .
        norm_cast at h
        tauto
    have f1:= lemma_1 1 2 a (by tauto)
    have g1:= lemma_2 (⌊1 / a⌋ + 1) (⌈2 / a⌉ - 1)
    rw [f1] at h1
    clear f1
    rw [Set.encard_coe_eq_coe_finsetCard] at h1
    norm_cast at h1
    zify at h1
    rw [g1] at h1
    clear g1
    have f2:= lemma_1 2 3 a (by tauto)
    have g2:= lemma_2 (⌊2 / a⌋ + 1) (⌈3 / a⌉ - 1)
    rw [f2]
    clear f2
    rw [Set.encard_coe_eq_coe_finsetCard]
    norm_cast
    zify
    rw [g2]
    clear g2
    ring_nf at h1
    ring_nf
    set x:= a⁻¹
    replace ha: 0 < x := by
      simp [x]
      clear *- ha
      tauto
    clear_value x
    set j:= ⌈x * 2⌉ - ⌊x⌋
    set s:= ⌈x * 3⌉ - ⌊x * 2⌋
    clear h2
    suffices s = 3 ∨ s = 4 ∨ s = 5 by
      rcases this with v | v | v
      all_goals simp [v]
    replace h1: j = 4 := by
      suffices (-1 + j) ⊔ 0 = -1 + j by
        simp [this] at h1
        linarith
      simp
      clear *- h1
      clear_value j
      omega
    simp [j] at h1
    clear_value j

    -- we show that 5 / 2 ≤ x
    have lx: 5 / 2 ≤ x := by
      have l:= Int.ceil_le_floor_add_one (x * 2)
      replace l: 3 ≤ ⌊x * 2⌋ - ⌊x⌋ := by
        clear *- l h1
        linarith
      have f1:= Int.floor_le (x * 2)
      have f2: 0 ≤ ⌊x⌋ := by
        rw [Int.floor_nonneg]
        linarith
      have f3: 3 ≤ x * 2 := by
        rify at l f2
        linarith
      have f4: 1 ≤ x := by
        linarith
      have f5: 1 ≤ ⌊x⌋ := by
        rw [Int.le_floor]
        simp
        tauto
      have f6: 4 ≤ ⌊x * 2⌋ := by
        clear *- f5 l
        omega
      replace f6: 2 ≤ x := by
        clear *- f6 f1
        rify at f6
        linarith
      have f7: 2 ≤ ⌊x⌋ := by
        rw [Int.le_floor]
        simp
        tauto
      have f8: 5 ≤ ⌊x * 2⌋ := by
        clear *- f7 l
        omega
      clear *- f8 f1
      rify at f8
      linarith

    -- then we show that x ≤ 4
    have rx: x ≤ 4 := by
      have g1:= Int.floor_le x
      have g2:= Int.le_ceil (x * 2)
      rify at h1
      linarith

    -- it suffices to show that 2 < s < 6
    have l1: s < 6 := by
      simp [s]
      have g1:= Int.lt_floor_add_one (x * 2)
      have g2:= Int.ceil_lt_add_one (x * 3)
      rify
      by_cases r: x = 4
      .
        simp [r]
        norm_num
      .
        replace r: x < 4 := by
          by_contra! o
          replace o: x = 4 := by linarith
          tauto
        clear *- g1 g2 r
        linarith
    have l2: 2 < s := by
      have g1:= Int.floor_le (x * 2)
      have g2:= Int.le_ceil (x * 3)
      simp [s]
      rify
      clear *- g1 g2 lx
      linarith
    clear *- l1 l2
    omega


  -- the backward direction, show that 2 m's and 3 m's and 4 m's are all possible
  .
    intro h
    simp at h
    rcases h with h | h | h

    -- case k = 2
    .
      simp [h]
      use (3 / 8)
      refine ⟨(by norm_num), ?_, ?_⟩
      .
        suffices {n: ℤ | (1: ℝ) < 3 / 8 * ↑n ∧ 3 / 8 * ↑n < (2: ℝ)} = {3, 4, 5} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          intro f
          simp at f
          simp
          suffices 2 < n ∧ n < 6 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f | f
          all_goals simp [f]; norm_num
      .
        suffices {m: ℤ | (2: ℝ) < 3 / 8 * ↑m ∧ 3 / 8 * ↑m < (3: ℝ)} = {6, 7} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          clear h
          intro f
          simp at f
          simp
          suffices 5 < n ∧ n < 8 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f
          all_goals simp [f]; norm_num

    -- k = 3
    .
      simp [h]
      use 1 / 4
      refine ⟨(by norm_num), ?_, ?_⟩
      .
        suffices {n: ℤ | (1: ℝ) < 1 / 4 * ↑n ∧ 1 / 4 * ↑n < (2: ℝ)} = {5, 6, 7} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          intro f
          simp at f
          simp
          suffices 4 < n ∧ n < 8 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f | f
          all_goals simp [f]; norm_num
      .
        suffices {m: ℤ | (2: ℝ) < 1 / 4 * ↑m ∧ 1 / 4 * ↑m < (3: ℝ)} = {9, 10, 11} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          clear h
          intro f
          simp at f
          simp
          suffices 8 < n ∧ n < 12 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f | f
          all_goals simp [f]; norm_num

    -- k = 4
    .
      simp [h]
      use 5 / 17
      refine ⟨(by norm_num), ?_, ?_⟩
      .
        suffices {n: ℤ | (1: ℝ) < 5 / 17 * ↑n ∧ 5 / 17 * ↑n < (2: ℝ)} = {4, 5, 6} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          intro f
          simp at f
          simp
          suffices 3 < n ∧ n < 7 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f | f
          all_goals simp [f]; norm_num
      .
        suffices {m: ℤ | (2: ℝ) < 5 / 17 * ↑m ∧ 5 / 17 * ↑m < (3: ℝ)} = {7, 8, 9, 10} by
          rw [this]
          simp [Set.encard]
        ext n
        constructor
        .
          clear h
          intro f
          simp at f
          simp
          suffices 6 < n ∧ n < 11 by omega
          rify
          refine ⟨(by linarith), (by linarith)⟩
        .
          intro h
          simp at h
          rcases h with f | f | f | f
          all_goals simp [f]; norm_num