import Mathlib

/-Three positive integers are such that they differ from each other by at most 6 . 
It is also known that the product of these three integers is 2808 . What is the smallest integer among them?-/

theorem number_theory_283900 {x y z: ℤ} (lx: 0 < x) (l1: x ≤ y) (l2: y ≤ z) (l3: z ≤ x + 6)
  (h: x * y * z = 2808): x = 12 := by

  -- we give the upper bound for x
  have u: x ≤ 14 := by
    have i: x ^ 3 ≤ 2808 := by
      calc
        x ^ 3 = x * x * x := by ring
            _ ≤ x * x * z := by nlinarith
            _ ≤ x * y * z := by nlinarith
            _ = 2808 := by rw [h]
    by_contra! o
    replace o: 15 ≤ x := by omega
    have c: 15 * 15 * 15 ≤ (2808: ℤ) := by
      calc
        15 * 15 * 15 ≤ x * 15 * 15 := by nlinarith
        _ ≤ x * x * 15 := by nlinarith
        _ ≤ x * x * x := by nlinarith
        _ = x ^ 3 := by ring
        _ ≤ 2808 := by nlinarith
    norm_num at c
  
  -- we give the lower bound for x
  have l: 9 ≤ x := by
    by_contra! j
    replace j: z ≤ 14 := by omega
    have i: (2808: ℤ) ≤ 14 * 14 * 14 := by
      calc
        2808 = x * y * z := by rw [h]
        _ ≤ x * z * z := by nlinarith
        _ ≤ z * z * z := by nlinarith
        _ ≤ 14 * z * z := by nlinarith
        _ ≤ 14 * 14 * 14 := by nlinarith
    norm_num at i
  
  -- note that 2808 = 2^ 3 * 3 ^ 4 * 13, hence we must have x = 9 ∨ 12 ∨ 13
  have o: x = 9 ∨ x = 12 ∨ x = 13 := by
    have d: x ∣ 2808 := by
      rw [← h]
      rw [show x * y * z = x * (y * z) by ring]
      simp
    interval_cases x
    all_goals norm_num at d
    all_goals omega
  
  -- then we check the three cases
  rcases o with o | o | o

  -- case x = 9
  .
    simp [o] at *
    rw [show 9 * y * z = 9 * (y * z) by ring] at h
    replace h: y * z = 312 := by omega
    nlinarith

  -- case x = 12
  .
    exact o

  -- case x = 13
  .
    simp [o] at *
    rw [show 13 * y * z = 13 * (y * z) by ring] at h
    replace h: y * z = 216 := by omega
    have ly: y < 15 := by nlinarith
    interval_cases y
    .
      replace h: 13 ∣ 216 := by
        zify
        rw [← h]
        simp
      norm_num at h
    .
      replace h: 14 ∣ 216 := by
        zify
        rw [← h]
        simp
      norm_num at h
      
