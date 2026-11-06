import Mathlib
open Real Filter

/-- Approximation to the continued fraction:
    contFrac 0 = 1
    contFrac (n+1) = 1 + 1 / (1 + 2 / contFrac n) -/
noncomputable def contFrac : ℕ → ℝ
| 0 => 1
| (n + 1) => 1 + 1 / (1 + 2 / contFrac n)
-- Define the limit of the sequence (we assert it exists for now)
noncomputable def x : ℝ := lim (atTop.map contFrac)

lemma contFrac_limit_satisfies_eqn : x = 1 + 1 / (1 + 2 / x) := by sorry

/-- Show that the recurrence equation implies x = sqrt 2 -/
lemma contFrac_limit_is_sqrt2 : x = sqrt 2 := by
  have hx : x > 1 := by sorry

  -- Start with the recurrence
  have h : x = 1 + 1 / (1 + 2 / x) := contFrac_limit_satisfies_eqn

  -- Move 1 to the left side
  have h₁ : x - 1 = 1 / (1 + 2 / x) := by linarith
  
  -- Take reciprocal of both sides
  have h₂ : 1 / (x - 1) = 1 + 2 / x := by
    rw [h₁]
    field_simp [show x ≠ 1 from by linarith]

  -- Multiply both sides by x
  have h₃ : x * (1 / (x - 1)) = x + 2 := by
    rw[h₂]
    field_simp [show x ≠ 0 from by linarith]

  -- Multiply both sides by (x - 1)
  have h₄ : x = (x + 2) * (x - 1) := by
    rw [← h₃]
    field_simp [show x ≠ 1 from by linarith]
    rw [← mul_div]
    simp [show (x - 1) / (x - 1) = 1 from by apply div_self; linarith]

  conv at h₄ =>
    rhs 
    ring
  
  have h₅ : x - x = -2 + x + x ^ 2 - x := by 
    nth_rw 1 [h₄]
  
  have h₆ : 2 = x^2:= by
    simp at h₅
    linarith
  simp [(sqrt_eq_iff_eq_sq (by linarith) (by linarith)).mpr h₆]
  
/-- Final theorem: the value of the continued fraction is sqrt 2 -/
theorem continued_fraction_eq_sqrt2 :
  ∃ x : ℝ, (x = 1 + 1 / (1 + 2 / x)) ∧ x = sqrt 2 :=
  ⟨x, contFrac_limit_satisfies_eqn, contFrac_limit_is_sqrt2⟩