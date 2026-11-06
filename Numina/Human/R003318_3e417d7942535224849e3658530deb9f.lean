import Mathlib

set_option maxHeartbeats 400000

open Real

def M: Set (ℝ × ℝ) := { (x, y) | |tan (π * y)| + sin (π * x) ^ 2 = 0 ∧ cos (π * y) ≠ 0}

def N: Set (ℝ × ℝ) := { (x, y) | x ^ 2 + y ^ 2 ≤ 2}

-- we show a lemma to simplify M
lemma lemma_1 (x y: ℝ): |tan (π * y)| + sin (π * x) ^ 2 = 0 ↔ tan (π * y) = 0 ∧ sin (π * x) = 0 := by
  set p:= tan (π * y)
  set q:= sin (π * x)
  clear_value p q
  have r:= abs_nonneg p
  have s:= sq_nonneg q
  constructor
  .
    intro g
    constructor
    .
      suffices |p| = 0 by
        simp at this
        tauto
      nlinarith
    .
      suffices q ^ 2 = 0 by
        nlinarith
      nlinarith
  .
    intro h
    simp [h]

-- show two technical lemmas
lemma lemma_2: 1 = ((1: ℝ), (1: ℝ)) := by
  rfl

lemma lemma_3 (x1 y1 x2 y2: ℝ): (x1, y1) = (x2, y2) ↔ x1 = x2 ∧ y1 = y2 := by
  simp

-- give a simp conclusion for sin and cos
lemma lemma_4 (x: ℝ) (h: x = -1 ∨ x = 0 ∨ x = 1): sin (π * x) = 0 ∧ cos (π * x) ≠ 0 := by
  have f: sin (π * x) = 0 := by
    rw [Real.sin_eq_zero_iff]
    rcases h with h | h | h
    all_goals simp [h]
    .
      use -1
      norm_num
    .
      use 1
      norm_num
  simp [f]
  by_contra! g
  have c:= Real.sin_sq_add_cos_sq (π * x)
  simp [f, g] at c


/-If M={(x,y)∣∣tgπy∣+sin^2 πx=0},N={(x,y)∣ x^2 + y^2 ≤ 2},
then the number of elements in M∩N is (A) 4 (B) 5 . (C) 8 . (D) 9 . (China High School Mathematics League, 1993)-/

theorem algebra_169126: (M ∩ N).encard = 9 := by

  have g:= Real.pi_gt_d2

  -- we first compute the set
  have h_eq: M ∩ N = {(0, 0), (0, 1), (0, -1), (1, 0), (1, 1), (1, -1), (-1, 0), (-1, 1), (-1, -1)} := by
    ext ⟨x, y⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      simp
      simp [M] at h1
      rw [lemma_1] at h1
      rcases h1 with ⟨l1, l3⟩
      rcases l1 with ⟨l1, l2⟩
      rw [Real.tan_eq_zero_iff'] at l1
      obtain ⟨k, hk⟩ := l1
      rw [Real.sin_eq_zero_iff] at l2
      obtain ⟨m, hm⟩ := l2
      simp [N] at h2
      replace hk: y = ↑k := by
        clear *- hk g
        nlinarith
      replace hm: x = ↑m := by
        clear *- hm g
        nlinarith
      simp [hk, hm] at *
      replace h2: m ^ 2 + k ^ 2 ≤ 2 := by
        rify
        tauto
      have lm: m ≤ 1 := by
        clear *- h2
        nlinarith
      have rm: -1 ≤ m := by
        clear *- h2
        nlinarith
      have lk: k ≤ 1 := by
        clear *- h2
        nlinarith
      have rk: -1 ≤ k := by
        clear *- h2
        nlinarith
      have vk: k = -1 ∨ k = 0 ∨ k = 1 := by
        omega
      have vm: m = -1 ∨ m = 0 ∨ m = 1 := by
        omega
      clear *- vm vk
      rcases vk with f | f | f
      .
        rcases vm with g | g | g
        all_goals simp [f, g]
      .
        rcases vm with g | g | g
        all_goals simp [f, g]
      .
        rcases vm with g | g | g
        all_goals simp [f, g]
      tauto


    -- the backward direction
    .
      intro h
      simp at h
      simp [M, N]
      refine ⟨?_, (by rcases h with h | h | h | h | h | h | h | h | h; all_goals simp [h]; all_goals norm_num)⟩
      rw [lemma_1]
      have fx:= lemma_4 x (by rcases h with h | h | h | h | h | h | h | h | h; all_goals simp [h])
      have fy:= lemma_4 y (by rcases h with h | h | h | h | h | h | h | h | h; all_goals simp [h])
      clear h
      simp [Real.tan_eq_sin_div_cos, fx, fy]


  -- then we can count the number
  rw [h_eq]
  repeat rw [Set.encard_insert_of_not_mem]
  norm_num
  simp
  norm_num
  simp
  simp
  norm_num
  simp
  repeat rw [lemma_3]
  norm_num
  simp
  norm_num
  simp
  simp
  norm_num
  simp
  repeat rw [lemma_3]
  norm_num