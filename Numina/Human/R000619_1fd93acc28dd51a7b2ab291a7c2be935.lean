import Mathlib

/- Four positive integers $A$, $B$, $C$ and $D$ have a sum of 64. If $A+3 = B-3 = C \times 3 = D \div 3$, what is the value of the product $A \times B \times C \times D$? -/
theorem algebra_13322 {A B C D : ℤ} (h₀ : A > 0) (h₁ : B > 0) (h₂ : C > 0) (h₃ : D > 0)
    (h₄ : A + B + C + D = 64) (h₅ : A + 3 = B - 3) (h₆ : B - 3 = C * 3) (h₇ : C * 3 = (D / 3 : ℚ)) :
    A * B * C * D = 19440 := by
  qify at *
  have ⟨hA, hB, hC, hD⟩ : (A : ℚ) = 9 ∧ (B : ℚ) = 15 ∧ (C : ℚ) = 4 ∧ (D : ℚ) = 36 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      linarith
  norm_cast at hA hB hC hD
  subst_vars
  norm_num
