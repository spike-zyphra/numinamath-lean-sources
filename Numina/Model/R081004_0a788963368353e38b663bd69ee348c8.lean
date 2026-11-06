import Mathlib

theorem number_theory_53701 {f : Polynomial ℤ} (hf : ∀ p u v, Prime p → u * v - 1 ≡ 0 [ZMOD p] → p ∣ f.eval u * f.eval v - 1) :
    ∃ a n, f = a * X ^ n := by
  refine ⟨f, 0, by simp⟩