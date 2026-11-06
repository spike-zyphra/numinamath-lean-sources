import Mathlib

open Real

/- The monotonic decreasing interval of the function $y=2+3\sin x$ is \_\_\_\_.-/
theorem algebra_9205 (k : ℤ) {f : ℝ → ℝ} (hf : f = λ x => 2 + 3 * sin x) :
    MonotoneOn f {x | -(π/2) + 2*k*π ≤ x ∧ x ≤ π/2 + 2*k*π} := by
  -- y=sin(x) is monotone on [-π/2+2kπ, π/2+2kπ]
  -- Hence y=2+3sin(x) is monotone on [-π/2+2kπ, π/2+2kπ]
  have := Real.strictMonoOn_sin
  have sin_mono := StrictMonoOn.monotoneOn this
  intro a ha b hb hab
  simp at ha hb
  simp [hf]
  set x := a - k * (2 * π) with hx
  set y := b - k * (2 * π) with hy
  have hx1 : -(π / 2) ≤ x := by linarith
  have hx2 : x ≤ π / 2 := by linarith
  have hy1 : -(π / 2) ≤ y := by linarith
  have hy2 : y ≤ π / 2 := by linarith
  have hxy : x ≤ y := by linarith
  have : sin x ≤ sin y := by
    apply sin_mono
    . exact ⟨hx1, hx2⟩
    . exact ⟨hy1, hy2⟩
    . exact hxy
  -- Notice that y=sin(x) is periodic, we can deduce sin(a)≤sin(b) from sin(x)≤sin(y).
  rwa [hx, hy, sin_sub_int_mul_two_pi, sin_sub_int_mul_two_pi] at this
