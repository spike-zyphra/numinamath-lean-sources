import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_14638 (z : ℕ → ℂ) (hz1 : z 1 = 0)
  (hzn : ∀ n ≥ 1, z (n + 1) = (z n)^2 + I) :
  abs (z 111) = Real.sqrt 2 := by
  have h1 : z 1 = 0 := hz1
  have h2 : z 2 = I := by
    specialize hzn 1 (by norm_num)
    rw [h1] at hzn
    simpa using hzn
  have h3 : z 3 = -1 + I := by
    specialize hzn 2 (by norm_num)
    rw [h2] at hzn
    simp [pow_two, Complex.ext_iff] at hzn ⊢
    constructor <;> norm_num [hzn]
  have h4 : ∀ (m : ℕ), z (2 * m + 3) = -1 + I := by 
    intro m
    induction m with 
    | zero =>
      have h3 : z 3 = -1 + I := by 
        specialize hzn 2 (by norm_num)
        rw [h2] at hzn 
        simp [pow_two, Complex.ext_iff] at hzn ⊢
        constructor <;> norm_num [hzn]
      simpa using h3 
    | succ m ih =>
      have eq1 : z (2 * (m + 1) + 3) = z (2 * m + 5) := by ring_nf 
      have eq2 : z (2 * m + 4) = -I := by
        have eq3 : z (2 * m + 4) = (z (2 * m + 3)) ^ 2 + I := by 
          specialize hzn (2 * m + 3) (by omega) 
          simpa using hzn 
        rw [eq3, ih]
        simp [pow_two, Complex.ext_iff]
        <;> norm_num 
      have eq4 : z (2 * m + 5) = -1 + I := by 
        have eq5 : z (2 * m + 5) = (z (2 * m + 4)) ^ 2 + I := by 
          specialize hzn (2 * m + 4) (by omega) 
          simpa using hzn 
        rw [eq5, eq2] 
        simp [pow_two, Complex.ext_iff] 
        <;> norm_num 
      rw [eq1, eq4] 
  have h5 : z 111 = -1 + I := by 
    specialize h4 54 
    norm_num at h4 ⊢ 
    simpa using h4 
  rw [h5]
  simp [Complex.abs, Complex.normSq] 
  all_goals norm_num [Real.sqrt_sq]