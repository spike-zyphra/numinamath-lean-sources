import Mathlib

-- we prove a lemma to factorize the equation
lemma lemma_1 (x y: ℤ): 1 + 2013 * x + 2015 * y = x * y ↔ (x - 2015) * (y - 2013) = 4056196 := by
  constructor
  -- forward direction
  . 
    intro h
    ring_nf
    rw [← h]
    ring_nf

  -- backward direction
  . intro h
    nlinarith

/- Find all solutions in four-digit natural numbers for the equation
1+2013x+2015y=xy.-/

theorem number_theory_245394: {(x, y): ℤ × ℤ | 1000 ≤ x ∧ x < 10000
  ∧ 1000 ≤ y ∧ y < 10000 ∧ 1 + 2013 * x + 2015 * y = x * y} =
  {(2737, 7631), (3459, 4822), (4824, 3457), (7633, 2735), (6043, 3020), (4029, 4027), (3022, 6041)} := by

    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq]
    constructor

    -- the forward direction
    .
      intro h
      simp
      rcases h with ⟨lx, rx, ly, ry, h⟩
      rw [lemma_1] at h
      have hx: 2015 < x := by
        nlinarith
      have hy: 2013 < y := by
        nlinarith
      have d1: (x - 2015).natAbs ∈ Nat.divisors 4056196 := by
        simp
        zify
        rw [show |x - 2015| = x - 2015 by apply abs_of_nonneg (by nlinarith)]
        rw [← h]
        simp
      rw [show Nat.divisors 4056196 = {1, 2, 4, 19, 38, 53, 76, 106, 212, 361, 722,
      1007,1444,2014, 2809, 4028, 5618, 11236,19133, 38266, 53371,76532,106742, 
       213484, 1014049,2028098,4056196} 
          by native_decide] at d1
      simp at d1
      zify at d1
      rw [show |x - 2015| = x - 2015 by apply abs_of_nonneg (by nlinarith)] at d1
      rcases d1 with o | o | o | o | o | o | o | o | o | o | o | o | o 
      | o | o | o | o | o | o | o | o | o | o | o | o | o | o
      all_goals try nlinarith
      all_goals simp [o] at h
      .
        replace h: y = 7631 := by omega
        omega
      .
        replace h: y = 6041 := by omega
        omega
      .
        replace h: y = 4822 := by omega
        omega
      .
        omega
      .
        omega
      .
        replace h: y = 3020 := by omega
        omega
      .
        omega

        
    -- the backward direction
    .

      intro h
      simp at h
      rcases h with h | h | h | h | h | h | h
      .
        simp [h]
      . 
        simp [h]
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]