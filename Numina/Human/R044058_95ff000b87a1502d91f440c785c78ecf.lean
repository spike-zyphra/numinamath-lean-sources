import Mathlib

open Real Set
open scoped BigOperators

/-
Real numbers $x, y$ satisfy $x^{2}+x y+y^{2}=1, F(x, y)=x^{3} y+x y^{3}$.
(1) Prove: For any $x, y \in \mathbf{R}$ that meet the requirements, $F(x, y) \geqslant-2$.
(2) Find the maximum possible value of $F(x, y)$.
-/
theorem algebra_225137 {F : ℝ → ℝ → ℝ}
  (hF : F = λ x y => x^3 * y + x * y^3) :
  (∀ x y, x^2 + x * y + y^2 = 1 → F x y ≥ -2) ∧
  IsGreatest {z | ∃ x y, z = F x y ∧ x^2 + x * y + y^2 = 1} (2 / 9) := by

  constructor
  · -- Proof that for any x, y satisfying the constraint, F(x, y) ≥ -2
    intros x y h
    have h1 : F x y = x^3 * y + x * y^3 := by rw [hF]
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y + 1)]
  · -- Proof that 2/9 is the greatest value of F on the domain
    constructor
    · -- Show that 2/9 is attainable
      use 1 / Real.sqrt 3, 1 / Real.sqrt 3
      constructor
      · -- Show F(1/√3, 1/√3) = 2/9
        rw [hF]
        have h1 : (1 / Real.sqrt 3 : ℝ) ^ 3 * (1 / Real.sqrt 3 : ℝ) + (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) ^ 3 = 2 / 9 := by
          have h2 : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
            calc
              (1 / Real.sqrt 3 : ℝ) ^ 2 = (1 ^ 2) / (Real.sqrt 3 ^ 2) := by field_simp
              _ = 1 / 3 := by norm_num [Real.sq_sqrt]
          have h3 : (1 / Real.sqrt 3 : ℝ) ^ 3 * (1 / Real.sqrt 3 : ℝ) = 1 / 9 := by
            calc
              (1 / Real.sqrt 3 : ℝ) ^ 3 * (1 / Real.sqrt 3 : ℝ)
                  = ((1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring
              _ = (1 / 3) ^ 2 := by rw [h2]
              _ = 1 / 9 := by norm_num
          have h4 : (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) ^ 3 = 1 / 9 := by
            calc
              (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) ^ 3
                  = ((1 / Real.sqrt 3 : ℝ) ^ 2) ^ 2 := by ring
              _ = (1 / 3) ^ 2 := by rw [h2]
              _ = 1 / 9 := by norm_num
          linarith
        linarith [h1]
      · -- Show (1/√3)^2 + (1/√3)(1/√3) + (1/√3)^2 = 1
        have h2 : (1 / Real.sqrt 3 : ℝ) ^ 2 + (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) + (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 := by
          have h3 : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
            calc
              (1 / Real.sqrt 3 : ℝ) ^ 2 = (1 ^ 2) / (Real.sqrt 3 ^ 2) := by field_simp
              _ = 1 / 3 := by norm_num [Real.sq_sqrt]
          linarith [h3]
        linarith [h2]
    · -- Show that 2/9 is the maximum
      intro z hz
      rcases hz with ⟨x, y, hz_eq, h_constraint⟩
      rw [hz_eq, hF]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1 / 3), sq_nonneg (x^2 - y^2)]
