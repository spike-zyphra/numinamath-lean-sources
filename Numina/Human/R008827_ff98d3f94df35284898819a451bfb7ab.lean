import Mathlib

/- Let $f$ be a linear function for which $f(6)-f(2)=12$. What is $f(12)-f(2)?$ -/
theorem algebra_12177 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b) (h : f 6 - f 2 = 12) :
    f 12 - f 2 = 30 := by
  obtain ⟨a, b, rfl⟩ := hf
  simp_all
  linarith