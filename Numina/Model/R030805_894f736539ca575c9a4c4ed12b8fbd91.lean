import Mathlib

open Real Polynomial

theorem calculus_611098 : let f : ℝ → (Fin 2 → ℝ) := fun x => ![x, x ^ 4 / 8];
    IsLeast {d : ℝ | ∃ P ∈ f '' Set.univ, d =
    dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![0, 5 / 2])) ((EuclideanSpace.equiv (Fin 2) ℝ).symm P)} (√17 / 2) := by
  intro f
  constructor
  · -- Show that √17 / 2 is in the set.
    use ![2, 2]
    constructor
    · -- Show that ![2, 2] is in the image of f.
      use 2
      all_goals
        norm_num [f]
    · -- Show that the distance is √17 / 2.
    -- The distance from (0, 5/2) to (2, 2):
    -- sqrt((0-2)^2 + (5/2-2)^2) = sqrt(4 + (1/2)^2) = sqrt(4+1/4) = sqrt(17/4) = sqrt(17)/2
      have eq1 : dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![0, 5 / 2])) ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![2, 2]) = √17 / 2 := by
        simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.vecCons, Matrix.vecTail, Matrix.vecHead]
        ring_nf
        have h1 : Real.sqrt (17 / (4 : ℝ)) = Real.sqrt (17) / 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h1]
        <;> ring_nf <;> norm_num
      linarith [eq1]
  · -- Show that √17 / 2 is minimal.
    intro d hd
    rcases hd with ⟨P, hP, hdist⟩
    rcases hP with ⟨x, hx⟩ -- hx : x ∈ Set.univ ∧ f x = P
    -- Show that P 0 = x and P 1 = x^4/8
    have hfx_eq_P : f x = P := by
      have h1 : x ∈ Set.univ ∧ f x = P := by 
        simpa using hx
      exact h1.right
    have eq20 : P 0 = x := by
      have eq21 : f x = P := hfx_eq_P
      have eq22 : (f x) 0 = x := by 
        simp [f]
      have eq23 : P 0 = (f x) 0 := by 
        rw [eq21]
      rw [eq22] at eq23
      linarith
    have eq21 : P 1 = x ^ 4 / 8 := by
      have eq22 : f x = P := hfx_eq_P
      have eq23 : (f x) 1 = x ^ 4 / 8 := by 
        simp [f]
        all_goals try ring
      have eq24 : P 1 = (f x) 1 := by 
        rw [eq22]
      rw [eq23] at eq24
      linarith
    have eq4 : dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![0, 5 / 2])) ((EuclideanSpace.equiv (Fin 2) ℝ).symm P) = Real.sqrt ((P 0 ^ 2 + (P 1 - (5 / 2 : ℝ)) ^ 2) ) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Matrix.vecCons, Matrix.vecTail, Matrix.vecHead]
      <;> ring
    rw [eq4] at hdist
    have h6 : P 0 ^ 2 + (P 1 - (5 / 2 : ℝ)) ^ 2 ≥ (17 / 4 : ℝ) := by
      rw [eq20, eq21]
      nlinarith [sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 4 - 16), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 + 2), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg (x ^ 2 + 2 * x), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 4 - 32)]
    have h7 : Real.sqrt (P 0 ^ 2 + (P 1 - (5 / 2 : ℝ)) ^ 2) ≥ Real.sqrt ((17 / 4 : ℝ)) := by 
      apply Real.sqrt_le_sqrt
      linarith [h6]
    have h8 : Real.sqrt ((17 / 4 : ℝ)) = (Real.sqrt 17 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h10 : Real.sqrt (P 0 ^ 2 + (P 1 - (5 / 2 : ℝ)) ^ 2) ≥ (Real.sqrt 17 / 2 : ℝ) := by
      rw [h8] at h7
      linarith
    linarith [h10, hdist]