import Mathlib

-- we first prove the case when c ≤ b ≤ a
lemma lemma_1 (a b c: ℤ) (l1: 0 < c) (l2: c ≤ b) (l3: b ≤ a)
  (p1: IsCoprime a b) (p2: IsCoprime b c) (p3: IsCoprime c a)
  (h1: a ^ 2 ∣ (b ^ 3 + c ^ 3)) (h2: b ^ 2 ∣ (a ^ 3 + c ^ 3))
  (h3: c ^ 2 ∣ (a ^ 3 + b ^ 3)): (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 3 ∧ b = 2 ∧ c = 1) := by

  by_contra! f
  -- we show the key divisibility
  have d: a ^ 2 * b ^ 2 * c ^ 2 ∣ a ^ 3 + b ^ 3 + c ^ 3 := by
    apply IsCoprime.mul_dvd
    .
      apply IsCoprime.mul_left
      apply IsCoprime.symm at p3
      apply IsCoprime.pow p3
      apply IsCoprime.pow p2

    .
      apply IsCoprime.mul_dvd
      .
        apply IsCoprime.pow p1
      .
        rw [show a ^ 3 + b ^ 3 + c ^ 3 = a ^ 3 + (b ^ 3 + c ^ 3) by ring]
        apply dvd_add
        rw [show a ^ 3 = a ^ 2 * a by ring]
        simp
        exact h1
      .
        rw [show a ^ 3 + b ^ 3 + c ^ 3 = b ^ 3 + (a ^ 3 + c ^ 3) by ring]
        apply dvd_add
        rw [show b ^ 3 = b ^ 2 * b by ring]
        simp
        exact h2
    .
      apply dvd_add
      exact h3
      rw [show c ^ 3 = c ^ 2 * c by ring]
      simp

  clear h2 h3
  have s2: c ^ 3 ≤ b ^ 3 := by
    rw [pow_le_pow_iff_left₀]
    exact l2
    linarith
    linarith
    norm_num
  have s3: b ^ 3 ≤ a ^ 3 := by
    rw [pow_le_pow_iff_left₀]
    exact l3
    linarith
    linarith
    norm_num
  have f2: 0 ≤ a ^ 2 * b ^ 2 * c ^ 2 := by
      have g1: 0 ≤ a ^ 2 * b ^ 2 := by
        nlinarith
      nlinarith
  have r1:= d
  apply exists_eq_mul_right_of_dvd at r1
  obtain ⟨r, r1⟩ := r1
  have lr: 0 < r := by
    have f1: 0 ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
      nlinarith
    nlinarith
  replace lr: 1 ≤ r := by omega
  replace r1: a ^ 2 * b ^ 2 * c ^ 2  ≤ (a ^ 3 + b ^ 3 + c ^ 3) := by
    rw [r1]
    nlinarith
  have r2: a ^ 2 * b ^ 2 * c ^ 2 ≤ 3 * a ^ 3 := by
    nlinarith
  replace r2: b ^ 2 * c ^ 2 ≤ 3 * a := by
    nlinarith
  have r3:= h1
  apply exists_eq_mul_right_of_dvd at r3
  obtain ⟨s, r3⟩ := r3
  have ls: 0 < s := by
    have f1: 0 ≤ b ^ 3 + c ^ 3 := by
      nlinarith
    nlinarith
  replace ls: 1 ≤ s := by omega
  replace r3: a ^ 2 ≤ b ^ 3 + c ^ 3 := by
    rw [r3]
    nlinarith
  clear ls lr
  have r4: b ^ 4 * c ^ 4 ≤ 9 * a ^ 2 := by
    nlinarith
  replace r4: b ^ 4 * c ^ 4 ≤ 9 * (b ^ 3 + c ^ 3) := by
    nlinarith
  replace r4: b ^ 4 * c ^ 4 ≤ 18 * b ^ 3 := by
    nlinarith

  -- then we get the key upper bound
  replace r4: b * c ^ 4 ≤ 18 := by
    nlinarith
  have lc: c < 2 := by
    by_contra! lc
    have u: 2 ^ 4 ≤ c ^ 4 := by
      rw [pow_le_pow_iff_left₀]
      exact lc
      norm_num
      omega
      norm_num
    nlinarith [r3, u]
  have vc: c = 1 := by omega
  simp [vc] at *
  clear p2 p3 l1 lc vc
  replace r1: a ^ 2 * b ^ 2 < 2 * a ^ 3 := by
    suffices a ^ 3 + b ^ 3 + 1 < 2 * a ^ 3 by
      nlinarith
    suffices b ^ 3 + 1 < a ^ 3 by linarith
    have i: b + 1 ≤ a := by
      by_contra! i
      replace i: a = b := by omega
      simp [i] at p1
      rw [isCoprime_self] at p1
      apply Int.isUnit_eq_one_or at p1
      rcases p1 with j | j
      .
        simp [j] at i
        simp [i, j] at f
      .
        simp [j] at l2
    suffices b ^ 3 + 1 < (b + 1) ^ 3 by
      have v: (b + 1) ^ 3 ≤ a ^ 3 := by
        rw [pow_le_pow_iff_left₀]
        exact i
        omega
        omega
        norm_num
      linarith
    ring_nf
    nlinarith
  replace r1: b ^ 2 < 2 * a := by
    nlinarith [r1]
  replace r1: b ^ 4 < 4 * a ^ 2 := by
    nlinarith [r1]

  -- obtain the upper bound for b
  have g: b ^ 4 < 4 * (b ^ 3 + 1) := by linarith
  have rb: b < 5 := by nlinarith [g]
  interval_cases b

  -- case b = 1.
  .
    simp at r3
    have sa: a < 2 := by nlinarith [r3]
    have va: a = 1 := by omega
    simp [va] at f

  -- case b = 2.
  .
    clear h1 d s2 f2 r2 p1
    have sa: a < 4 := by nlinarith
    have la: 2 < a := by nlinarith
    have va: a = 3 := by omega
    simp [va] at f

  -- case b = 3
  .
    clear rb g r4 f2 s2 d
    have sa: a < 6 := by nlinarith [r3]
    interval_cases a
    .
      norm_num at p1
    .
      norm_num at h1
    .
      norm_num at h1

  --  case b = 4
  .
    clear s3 l2 d s2 f r4 g rb
    have sa: a < 9 := by nlinarith [r3]
    have la: 5 < a := by nlinarith [r2]
    interval_cases a
    .
      norm_num at p1
    .
      norm_num at h1
    .
      norm_num at p1


/-Given that a, b, and c are pairwise coprime positive integers, and satisfy
a ^ 2 ∣ (b ^ 3 + c ^ 3)
b ^ 2 ∣ (a ^ 3 + c ^ 3)
c ^ 2 ∣ (a ^ 3 + b ^ 3),
Find the values of a, b, and c.-/

theorem number_theory_316998: {(a, b, c): ℤ × ℤ × ℤ | 0 < a ∧ 0 < b ∧ 0 < c ∧ IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime c a ∧
  a ^ 2 ∣ (b ^ 3 + c ^ 3) ∧ b ^ 2 ∣ (a ^ 3 + c ^ 3) ∧ c ^ 2 ∣ (a ^ 3 + b ^ 3)}
    = {(1, 1, 1),(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)} := by

  ext ⟨a, b, c⟩
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    rcases h with ⟨l1, l2, l3, p1, p2, p3, h1, h2, h3⟩

    -- then we consider all orderings of a, b, c to apply lemma_1
    have u: (c ≤ b ∧ b ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨ (b ≤ c ∧ c ≤ a)
      ∨ (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b):= by omega
    rcases u with u | u | u | u | u | u

    -- case 1: c ≤ b ∧ b ≤ a
    .
      have i:= lemma_1 a b c (by omega) (by omega) (by omega) p1 p2 p3 h1 h2 h3
      rcases i with i | i
      all_goals simp [i]

    -- case 2: c ≤ a ∧ a ≤ b
    .
      have i:= lemma_1 b a c (by omega) (by omega) (by omega)
      apply IsCoprime.symm at p1
      apply IsCoprime.symm at p2
      apply IsCoprime.symm at p3
      rw [show a ^ 3 + b ^ 3 = b ^ 3 + a ^ 3 by ring] at h3
      simp [p1, p2, p3, h1, h2, h3] at i
      rcases i with i | i
      all_goals simp [i]

    -- case 3: b ≤ a ∧ a ≤ c
    .
      have i:= lemma_1 c a b (by omega) (by omega) (by omega)
      rw [show b ^ 3 + c ^ 3 = c ^ 3 + b ^ 3 by ring] at h1
      rw [show a ^ 3 + c ^ 3 = c ^ 3 + a ^ 3 by ring] at h2
      simp [p1, p2, p3, h1, h2, h3] at i
      rcases i with i | i
      all_goals simp [i]

    -- case 4: b ≤ c ∧ c ≤ a
    .
      have i:= lemma_1 a c b (by omega) (by omega) (by omega)
      apply IsCoprime.symm at p1
      apply IsCoprime.symm at p2
      apply IsCoprime.symm at p3
      rw [show b ^ 3 + c ^ 3 = c ^ 3 + b ^ 3 by ring] at h1
      simp [p1, p2, p3, h1, h2, h3] at i
      rcases i with i | i
      all_goals simp [i]

    -- case 5: a ≤ b ∧ b ≤ c
    .
      have i:= lemma_1 c b a (by omega) (by omega) (by omega)
      apply IsCoprime.symm at p1
      apply IsCoprime.symm at p2
      apply IsCoprime.symm at p3
      rw [show a ^ 3 + b ^ 3 = b ^ 3 + a ^ 3 by ring] at h3
      rw [show b ^ 3 + c ^ 3 = c ^ 3 + b ^ 3 by ring] at h1
      rw [show a ^ 3 + c ^ 3 = c ^ 3 + a ^ 3 by ring] at h2
      simp [p1, p2, p3, h1, h2, h3] at i
      rcases i with i | i
      all_goals simp [i]

    -- case 6: a ≤ c ∧ c ≤ b
    .
      have i:= lemma_1 b c a (by omega) (by omega) (by omega)
      rw [show a ^ 3 + c ^ 3 = c ^ 3 + a ^ 3 by ring] at h2
      rw [show a ^ 3 + b ^ 3 = b ^ 3 + a ^ 3 by ring] at h3
      simp [p1, p2, p3, h1, h2, h3] at i
      rcases i with i | i
      all_goals simp [i]


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h | h | h
    all_goals simp [h]; norm_num