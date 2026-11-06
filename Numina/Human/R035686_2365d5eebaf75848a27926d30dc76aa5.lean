import Mathlib
open Complex


/- 30.28. Prove that if $x$ is a real number, then $e^{i x}=\cos x+i \sin x$ (Euler). -/
theorem algebra_230306 (x : ℝ) : Complex.exp (Complex.I * x) = Real.cos x + Complex.I * Real.sin x := by
  simp
  -- mathlib defines cos and sin in terms of exp
  unfold Complex.cos Complex.sin
  apply Eq.symm
  -- so we just calculate
  calc (cexp (↑x * I) + cexp (-↑x * I)) / 2 + I * ((cexp (-↑x * I) - cexp (↑x * I)) * I / 2)
  _ = (cexp (↑x * I) + cexp (-↑x * I)) / 2 + I * I * ((cexp (-↑x * I) - cexp (↑x * I)) / 2) := by ring_nf
  _ = (cexp (↑x * I) + cexp (-↑x * I)) / 2 - ((cexp (-↑x * I) - cexp (↑x * I)) / 2) := by simp; ring_nf
  _ = cexp (↑x * I) := by ring_nf
  _ = cexp (I * ↑x) := by ring_nf