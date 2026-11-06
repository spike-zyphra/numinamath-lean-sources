import Mathlib

/- Let real numbers  $a,b,c$ such that $\left| a-b \right|\ge \left| c \right|,\left| b-c \right|\ge \left| a \right|,\left| c-a \right|\ge \left| b \right|.$
Prove that $a=b+c$ or $b=c+a$ or $c=a+b.$ -/
theorem inequalities_71531 {a b c : ℝ} (h₀ : |a - b| ≥ |c|) (h₁ : |b - c| ≥ |a|)
    (h₂ : |c - a| ≥ |b|) :
    a = b + c ∨ b = c + a ∨ c = a + b := by 
  -- We consider all cases for the absolute values.
  cases' le_total 0 (a - b) with h₃ h₃ <;>   -- Absolute value logic and comparisons
    cases' le_total 0 (b - c) with h₄ h₄ <;>
    cases' le_total 0 (c - a) with h₅ h₅ <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos, abs_le] <;>
    first
    -- Check different linear cases
    | left; linarith
    | right; left; linarith
    | right; right; linarith