import Mathlib

/- Let $f(n)$ be the largest prime factor of $n^{2}+1$. Compute the least positive integer $n$ such that $f(f(n))=n$. -/
theorem number_theory_610317 (f : ℕ → ℕ) (hf : f = fun n ↦ ((n ^ 2 + 1).primeFactors.max).unbot' 0) :
    IsLeast { n | n > 0 ∧ f (f n) = n } 89 := by
  -- We have two goals
  constructor
  -- First, we show that 89 satisfies the property.
  . rw [hf]
    -- It is computably verifiable that f(f(89)) = 89.
    native_decide
  -- Second, we prove that any number satisfies the property is at least 89.
  . intro n ⟨h₁, h₂⟩
    -- That is equivalent to proving that any number less than 89 does not satisfy the property.
    contrapose! h₂
    -- So it suffices to show that f(f(n)) ≠ n for all 0 < n < 89.
    suffices H : ∀ n ∈ Finset.Ioo 0 89, f (f n) ≠ n from H n (Finset.mem_Ioo.mpr ⟨h₁, h₂⟩)
    -- It is computably verifiable that f(f(n)) ≠ n for all 0 < n < 89.
    rw [hf]
    native_decide
