import Mathlib

/- Example 1. Solve the equation
$$
(x+6)^{1991}+x^{1991}+2 x+6=0 .
$$ -/
theorem algebra_327523 :
    {x : ℝ | (x + 6) ^ 1991 + x ^ 1991 + 2 * x + 6 = 0} = {-3} := by
  -- x ↦ x ^ 1991 + x is an odd increasing function
  let f (x : ℝ) := x ^ 1991 + x
  have hf₁ : f.Odd := by
    simp [f]
    intro x
    simp [Odd.neg_pow (show Odd 1991 by decide)]
    ring
  have hf₂ : StrictMono f := by
    simp [f]
    refine StrictMono.add ?_ (fun _ _ h => h)
    exact Odd.strictMono_pow (by decide)
  ext x
  simp
  -- The equation is equivalent to f (x + 6) + f x = 0
  -- So it holds iff x + 6 + x = 0
  -- i.e. iff x = -3
  calc (x + 6) ^ 1991 + x ^ 1991 + 2 * x + 6 = 0
    _ ↔ f (x + 6) + f x = 0 := by
      congrm ?_ = 0
      simp [f, two_mul]
      ac_rfl
    _ ↔ f (x + 6) = f (-x) := by rw [hf₁]; exact add_eq_zero_iff_eq_neg
    _ ↔ x + 6 = -x := hf₂.injective.eq_iff
    _ ↔ x = -3 := by constructor <;> (intro; linarith)
