import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225137 {F : ℝ → ℝ → ℝ}
  (hF : F = λ x y => x^3 * y + x * y^3) :
  (∀ x y, x^2 + x * y + y^2 = 1 → F x y ≥ -2) ∧
  IsGreatest {z | ∃ x y, z = F x y ∧ x^2 + x * y + y^2 = 1} (2 / 9) := by
  constructor
  · -- Prove $F(x, y) \geq -2$.
    intros x y h
    have h1 : F x y = x^3 * y + x * y^3 := by rw [hF]
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y + 1), sq_nonneg (x * y - 1 / 3)]
    
  · -- Show that $2/9$ is the greatest value.
    constructor
    · -- Show $\frac{2}{9}$ is in the set.
      use Real.sqrt (1 / 3), Real.sqrt (1 / 3)
      constructor
      · -- Show $z = F(x, y)$.
        rw [hF]
        have h1 : (Real.sqrt (1 / 3)) ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg (1 / 3)]
      · -- Show $x^2 + x * y + y^2 = 1$.
        have h1 : (Real.sqrt (1 / 3)) ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg (1 / 3)]
    
    · -- Show that $2/9$ is greatest.
      intro z h
      rcases h with ⟨x, y, hz, hxy⟩
      have h_eq : z = x^3 * y + x * y^3 := by
        have h1 : F x y = x^3 * y + x * y^3 := by 
          rw [hF]
        linarith [hz, h1]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1 / 3), sq_nonneg (x ^ 2 + y ^ 2 - 2 / 3), h_eq]