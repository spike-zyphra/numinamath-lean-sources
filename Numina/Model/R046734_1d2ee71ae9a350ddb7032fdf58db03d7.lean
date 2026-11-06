import Mathlib

open Real

theorem algebra_317397 (t : ℝ → ℝ) (ht : t = fun x => (1/2)^x + (2/3)^x + (5/6)^x) :
    ∑ᶠ x ∈ {x | (t x - 1)*(t x - 2)*(t x - 3) = 0}, x = 4 := by
  have tmo : StrictAnti t := by 
    rw [ht]
    unfold StrictAnti
    intro x y h
    -- show t(x) > t(y)
    have h41 : (1 / 2 : ℝ) ^ x - (1 / 2 : ℝ) ^ y > 0 := by
      have h11 : (1 / 2 : ℝ) ^ x > (1 / 2 : ℝ) ^ y := by 
        have h1 : (1 / 2 : ℝ) ^ x = (2 : ℝ) ^ (-x : ℝ) := by 
          rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          · ring
          · norm_num
        have h2 : (1 / 2 : ℝ) ^ y = (2 : ℝ) ^ (-y : ℝ) := by 
          rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          · ring
          · norm_num
        rw [h1, h2]
        apply Real.rpow_lt_rpow_of_exponent_lt
        · norm_num
        · linarith
      linarith [h11]
    -- prove the same for (2/3)^x and (5/6)^x
    have h42 : (2 / 3 : ℝ) ^ x - (2 / 3 : ℝ) ^ y > 0 := by
      have h11 : (2 / 3 : ℝ) ^ x > (2 / 3 : ℝ) ^ y := by 
        have h1 : (2 / 3 : ℝ) ^ x = ((2 / 3 : ℝ) ^ (-1 : ℝ)) ^ (-x : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h2 : (2 / 3 : ℝ) ^ y = ((2 / 3 : ℝ) ^ (-1 : ℝ)) ^ (-y : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        rw [h1, h2]
        have h3 : ((2 / 3 : ℝ) ^ (-1 : ℝ) : ℝ) > 1 := by
          norm_num
        have h6 : (-x : ℝ) > (-y : ℝ) := by linarith
        have h7 : ((2 / 3 : ℝ) ^ (-1 : ℝ) : ℝ) ^ (-x) > ((2 / 3 : ℝ) ^ (-1 : ℝ) : ℝ) ^ (-y) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        linarith
      linarith [h11]
    have h43 : (5 / 6 : ℝ) ^ x - (5 / 6 : ℝ) ^ y > 0  := by
      have h11 : (5 / 6 : ℝ) ^ x > (5 / 6 : ℝ) ^ y := by 
        have h1 : (5 / 6 : ℝ) ^ x = ((5 / 6 : ℝ) ^ (-1 : ℝ)) ^ (-x : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        have h2 : (5 / 6 : ℝ) ^ y = ((5 / 6 : ℝ) ^ (-1 : ℝ)) ^ (-y : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        rw [h1, h2]
        have h3 : ((5 / 6 : ℝ) ^ (-1 : ℝ) : ℝ) > 1 := by
          norm_num
        have h6 : (-x : ℝ) > (-y : ℝ) := by linarith
        have h7 : ((5 / 6 : ℝ) ^ (-1 : ℝ) : ℝ) ^ (-x) > ((5 / 6 : ℝ) ^ (-1 : ℝ) : ℝ) ^ (-y) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        linarith
      linarith [h11]
    have h14 : ((1 / 2 : ℝ) ^ x + (2 / 3 : ℝ) ^ x + (5 / 6 : ℝ) ^ x) - ((1 / 2 : ℝ) ^ y + (2 / 3 : ℝ) ^ y + (5 / 6 : ℝ) ^ y) > 0 := by
      linarith
    simpa using h14
  have teq1 : t 0 = 3 := by norm_num [ht]
  have teq2 : t 1 = 2 := by norm_num [ht]
  have teq3 : t 3 = 1 := by norm_num [ht]
  have h1 : {x : ℝ | (t x - 1)*(t x - 2)*(t x - 3) = 0} = {0, 1, 3} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    have h3 : (t x - 1) * (t x - 2) * (t x - 3) = 0 ↔ t x = 1 ∨ t x = 2 ∨ t x = 3 := by 
      constructor
      · -- Forwardstep: from equation to disjunction 
        intro h
        cases' (mul_eq_zero.mp h) with h1 h2
        · 
          cases' (mul_eq_zero.mp h1) with h11 h12
          · -- case $t x - 1 = 0$
            left
            linarith
          · -- case $t x - 2 = 0$
            right
            left
            linarith
        · -- Case $t x - 3 = 0$
          right
          right
          linarith
      · -- Backstep: from disjunction to equation 
        rintro (h | h | h)
        · -- Case $t x = 1$
          rw [h]
          norm_num
        · -- Case $t x = 2$
          rw [h]
          norm_num
        · -- Case $t x = 3$
          rw [h]
          norm_num
    rw [h3]
    constructor
    · -- Forward: points satisfying the equation are in {0,1,3}
      intro h
      rcases h with ht1 | ht2 | ht3
      · -- Case t(x) = 1: x = 3
        have h_eq1 : x = 3 := by
          have h1 : t x = 1 := by linarith
          by_cases h' : x < (3 : ℝ)
          · -- Suppose x < 3, show contradiction by proving t(x) > 1
            have h2 : t x > 1 := by
              nlinarith [show t x > t 3 by apply tmo; nlinarith, teq3]
            linarith
          by_cases h' : x > (3 : ℝ)
          · -- Suppose x > 3, show contradiction by proving t(x) < 1
            have h4 : t x < 1 := by
              nlinarith [show t x < t 3 by apply tmo; nlinarith, teq3]
            linarith
          linarith
        simp [h_eq1]
      · -- Case t(x) = 2: x = 1
        have h_eq2 : x = 1 := by
          have h2 : t x = 2 := by linarith
          by_cases h' : x < (1 : ℝ)
          · -- Suppose x < 1, show contradiction by proving t(x) > 2
            have h2 : t x > 2 := by
              nlinarith [show t x > t 1 by apply tmo; nlinarith, teq2]
            linarith
          by_cases h' : x > (1 : ℝ)
          · -- Suppose x > 1, show contradiction by proving t(x) < 2
            have h4 : t x < 2 := by
              nlinarith [show t x < t 1 by apply tmo; nlinarith, teq2]
            linarith
          linarith
        simp [h_eq2]
      · -- Case t(x) = 3: x = 0
        have h_eq3 : x = 0 := by
          have h3 : t x = 3 := by linarith
          by_cases h' : x > (0 : ℝ)
          · -- Suppose x > 0, show contradiction by proving t(x) < 3
            have h4 : t x < 3 := by
              nlinarith [show t x < t 0 by apply tmo; nlinarith, teq1]
            linarith
          by_cases h' : x < (0 : ℝ)
          · -- Suppose x < 0, show contradiction by proving t(x) > 3
            have h4 : t x > 3 := by
              nlinarith [show t x > t 0 by apply tmo; nlinarith, teq1]
            linarith
          linarith
        simp [h_eq3]
    · -- Backward: points in {0,1,3} satisfy the equation
      rintro (rfl | rfl | rfl)
      all_goals try norm_num [ht]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> norm_num