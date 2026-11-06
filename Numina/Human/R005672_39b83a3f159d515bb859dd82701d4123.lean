import Mathlib
/-In equilateral triangle $A B C$ with side length 2 , let the parabola with focus $A$ and directrix $B C$ intersect sides $A B$ and $A C$ at $A_{1}$ and $A_{2}$, respectively. Similarly, let the parabola with focus $B$ and directrix $C A$ intersect sides $B C$ and $B A$ at $B_{1}$ and $B_{2}$, respectively. Finally, let the parabola with focus $C$ and directrix $A B$ intersect sides $C A$ and $C B$ at $C_{1}$ and $C_{2}$, respectively.
Find the perimeter of the triangle formed by lines $A_{1} A_{2}, B_{1} B_{2}, C_{1} C_{2}$.-/
theorem geometry_609352 (AB BC CD AA1 A1B A1M AP AD OA OP OD L S : ℝ)  
  (h_AB    : AB = 2)                  -- Length of side AB is 2
  (h_BC    : BC = 2)                  -- Length of side BC is 2
  (h_CD    : CD = 2)                  -- Length of side CD is 2
  (h_sum_AB: AA1 + A1B = AB)          -- Point A1 is on AB
  (h_A1M   : A1M = AA1)               -- By parabola property, distance from A1 to focus equals distance to directrix
  (h_A1M_rate : (Real.sqrt 3) * A1B = 2 * A1M) -- 60-degree right triangle proportion for triangle A1BM
  (h_AP_rate  : 2 * AP = (Real.sqrt 3) * AA1)  -- 60-degree right triangle proportion for triangle AA1P
  (h_OA    : (Real.sqrt 3) * OA = AB) -- 60-degree right triangle proportion for centroid distance in equilateral triangle
  (h_sum_OA: AP + OP = OA)            -- Point P is on OA
  (h_AD    : 2 * AD = (Real.sqrt 3) * AB) -- 60-degree right triangle proportion for triangle ABD
  (h_sum_AD: OA + OD = AD)            -- Point O is on AD
  (h_L     : OP / OD = L / AB)        -- Proportion of distances from centroid to sides equals proportion of side lengths
  (h_S     : S = 3 * L)               -- Perimeter of equilateral triangle is 3 times side length
: S = 66 - 36 * Real.sqrt 3  := by
  -- Step 1: Use parabola theorem to find AA1 length
  rw [h_AB] at h_sum_AB
  have h_sum_AB' : A1B = 2 - AA1 := by linarith
  rw [h_A1M, h_sum_AB'] at h_A1M_rate
  have h_AA1 : AA1 = 4 * Real.sqrt 3 - 6 := by
    ring_nf at h_A1M_rate
    have h1 : 2 * √3 = AA1 * (2 + √3) := by linarith
    have h_denom_neq : 2 + Real.sqrt 3 ≠ 0 := by positivity
    rw [eq_comm] at h1 
    rw [(eq_div_iff_mul_eq h_denom_neq).mpr h1]
    rw [div_eq_iff h_denom_neq]
    ring_nf
    simp [mul_assoc, mul_comm, mul_left_comm, ← pow_two]
    norm_num

  -- Step 2: Find AP length using 60-degree right triangle proportion
  have h_AP : AP = 6 - 3 * Real.sqrt 3  := by
    rw [h_AA1] at h_AP_rate
    ring_nf at h_AP_rate
    linarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num)] 

  -- Step 3: Find OA using 60-degree right triangle proportion
  have h_AD' : AD = Real.sqrt 3 := by
    rw [h_AB] at h_AD
    linarith
  have h_OA' : OA = 2 * Real.sqrt 3 / 3 := by
    rw [h_AB,mul_comm] at h_OA
    have h_denom_neq : Real.sqrt 3 ≠ 0 := by positivity
    rw [(eq_div_iff_mul_eq h_denom_neq).mpr h_OA]
    field_simp [mul_assoc] at h_OA ⊢

  -- Step 4: Find OP and OD using proportions
  have h_OP : OP = 11 * Real.sqrt 3 / 3 - 6 := by
    rw [h_AP,h_OA'] at h_sum_OA
    linarith
  have h_OD : OD = Real.sqrt 3 / 3 := by
    rw [h_OA', h_AD'] at h_sum_AD
    linarith

  -- Step 5: Find L using proportion of distances
  have h_L' : L = 22 - 12 * Real.sqrt 3 := by
    rw [h_OD, h_OP, h_AB] at h_L
    rw [eq_comm] at h_L
    field_simp at h_L 
    have h_denom_neq : Real.sqrt 3 ≠ 0 := by norm_num [Real.sqrt_eq_zero]
    rw [(eq_div_iff_mul_eq h_denom_neq).mpr h_L]
    have h : Real.sqrt 3 ≠ 0 := by norm_num [Real.sqrt_eq_zero]
    field_simp [h]
    ring_nf
    norm_num
    ring

  -- Final step: Calculate perimeter S
  rw [h_L'] at h_S
  linarith
