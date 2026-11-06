import Mathlib

theorem algebra_22077 {f : ℝ → ℝ} (hf : f = λ x => -3 * x ^ 2 + 36 * x - 7) : IsLeast {c : ℝ | Function.HasLeftInverse (Set.restrict {x | c ≤ x} f)} 6 := by
  simp [← Function.injective_iff_hasLeftInverse, Function.Injective, hf]
  refine ⟨fun x hx y hy fxy => ?_, fun c hc => ?_⟩
  · nlinarith
  · by_contra! hc'
    specialize hc c (le_refl _) (12 - c) (by linarith) (by ring)
    linarith
