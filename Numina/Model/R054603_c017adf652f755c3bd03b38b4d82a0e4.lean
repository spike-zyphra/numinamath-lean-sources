import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156466 {H M mH : ℝ} (hM : M > 0) (hmH : mH > 0)
  (hH : H > 0) (f : ℝ → ℝ) (hf : f = λ h => (H * M / mH) * (Real.sqrt (1 + mH / M) - 1)) :
  IsLeast {x | ∃ h, x = f h ∧ h ∈ Icc 0 H} (f 0) := by 
  constructor 
  · -- Show that f(0) is in the set
    use 0
    constructor
    · -- Show that f(0) = f(0)
      rfl
    · -- Show that 0 ∈ Icc 0 H 
      exact ⟨by linarith, by linarith⟩
  · -- Show that f(0) is the least element in the set 
    intro x hx 
    rcases hx with ⟨h, rfl, ⟨hh1, hh2⟩⟩ 
    have h1 : f 0 = f h := by 
      simp [hf]
    linarith [h1]