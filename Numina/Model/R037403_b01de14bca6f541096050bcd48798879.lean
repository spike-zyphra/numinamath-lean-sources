import Mathlib

open Real Set
open scoped BigOperators

/- If the parabola $y=p{{x}^{2}}$ intersects with the square whose vertices are $A(1,1)$, $B(2,1)$, $C(2,2)$, and $D(1,2)$, then the range of the real number $p$ is ___          ___. -/
theorem algebra_10805 (p : ℝ) :
  (∃ x y, x ∈ Icc 1 2 ∧ y ∈ Icc 1 2 ∧ y = p * x ^ 2) ↔
  1 / 4 ≤ p ∧ p ≤ 2 := by
  constructor
  · -- Assume exists x y in the square such that y = p * x^2
    rintro ⟨x, y, ⟨hx1, hx2⟩, ⟨hy1, hy2⟩, h_eq⟩
    have h1 : 1 ≤ x ∧ x ≤ 2 := ⟨hx1, hx2⟩
    have h2 : 1 ≤ y ∧ y ≤ 2 := ⟨hy1, hy2⟩
    rw [h_eq] at h2
    have h3 : 1 ≤ p * x ^ 2 := by linarith
    have h4 : p * x ^ 2 ≤ 2 := by linarith
    have hx3 : x ^ 2 > 0 := by nlinarith
    have h5 : p ≥ 1 / 4 := by
      nlinarith [sq_nonneg (x), h3, sq_nonneg (x - 2), sq_nonneg (x - 1)]
    have h6 : p ≤ 2 := by
      nlinarith [sq_nonneg (x), h4, sq_nonneg (x - 2), sq_nonneg (x - 1)]
    constructor <;> linarith
  · -- Assume 1/4 ≤ p ≤ 2
    intro h
    rcases h with ⟨hp1, hp2⟩
    by_cases h1 : p ≤ 1 / 2
    · -- If p ≤ 1/2, then use x = 2
      use 2
      use 4 * p
      constructor
      · -- Show 2 ∈ [1, 2]
        exact ⟨by linarith, by linarith⟩
      constructor
      · -- Show 4p ∈ [1, 2]
        constructor
        · -- Show 1 ≤ 4p
          nlinarith
        · -- Show 4p ≤ 2
          nlinarith
      · -- Show 4p = p * 2 ^ 2
        ring_nf
    · -- If not p ≤ 1/2, so p > 1/2
      by_cases h2 : p ≤ 1
      · -- If 1/2 < p ≤ 1, then use x = sqrt(2)
        use Real.sqrt 2
        use 2 * p
        constructor
        · -- Show sqrt(2) ∈ [1, 2]
          constructor
          · -- Show 1 ≤ sqrt(2)
            have h3 : 1 < Real.sqrt 2 := by
              have h4 : 1 < (Real.sqrt 2 : ℝ) := by
                rw [Real.lt_sqrt] <;> norm_num
              linarith
            linarith
          · -- Show sqrt(2) ≤ 2
            have h5 : Real.sqrt 2 ≤ (2 : ℝ) := by
              have h6 : Real.sqrt 2 ≤ (2 : ℝ) := by
                rw [Real.sqrt_le_left] <;> norm_num
              linarith
            linarith
        constructor
        · -- Show 2p ∈ [1, 2]
          constructor
          · -- Show 1 ≤ 2p
            nlinarith
          · -- Show 2p ≤ 2
            nlinarith
        · -- Show 2p = p * (sqrt 2) ^ 2
          have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)
          field_simp [h3]
          all_goals nlinarith
      · -- If 1 < p ≤ 2, then use x = 1
        use 1
        use p
        constructor
        · -- Show 1 ∈ [1, 2]
          exact ⟨by linarith, by linarith⟩
        constructor
        · -- Show p ∈ [1, 2]
          constructor
          · -- Show 1 ≤ p
            nlinarith
          · -- Show p ≤ 2
            nlinarith
        · -- Show p = p * (1:ℝ) ^ 2
          ring_nf