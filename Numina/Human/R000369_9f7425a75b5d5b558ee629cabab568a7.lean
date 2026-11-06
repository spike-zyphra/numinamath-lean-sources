import Mathlib

open Real Complex

/-
Given that $m$ and $n$ are real numbers, if $\log_{2}(m^{2}-3m-3)+i\log_{2}(m-2)$ is a purely imaginary number, and the corresponding point of the complex number $z=m+ni$ is on the line $x+y-2=0$, then $|z|=$________.
-/
theorem algebra_9246 {m n : ℝ} {z : ℂ}
  (hm : m^2 - 3*m - 3 > 0 ∧ m - 2 > 0)
  (hc : (logb 2 (m^2 - 3*m - 3) + (logb 2 (m - 2)) * I).re = 0 ∧ (logb 2 (m^2 - 3*m - 3) + (logb 2 (m - 2)) * I).im ≠ 0)
  (hz : z = {re := m, im := n})
  (hmn : z.re + z.im - 2 = 0)
  : ‖z‖ = 2*√5 := by
  -- By definition, ‖z‖ = √(m * m + n * n)
  simp_all
  dsimp [Complex.abs]
  -- From the problem conditions, we clearly have m^2 - 3*m - 3 = 1 and m - 2 ≠ 1
  rcases hc with ⟨h1, h2⟩
  simp_all
  have : m^2 - 3*m - 3 > 0 := by linarith
  rcases h1 with h' | h'' | h''' <;> try linarith
  have _ : m > 2 := by linarith
  have h'' : m^2 - 3*m - 4 = 0 := by linarith
  -- Also, m^2 - 3*m - 4 = (m-4)*(m+1) holds
  have : m^2 - 3*m - 4 = (m - 4) * (m + 1) := by ring
  rw [this] at h''
  -- Therefore, m - 4 = 0 or m + 1 = 0
  have : m - 4 = 0 ∨ m + 1 = 0 := by simp_all
  rcases this with h₀ | h₁
  · -- Assume m = 4, from m + n - 2 = 0, we can get n = -2
    have hm : m = 4 := by linarith
    have : n = -2 := by linarith
    simp_all; ring_nf
    rw [(show (20 : ℝ) = 5 * 2^2 by ring)]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 5 by linarith)]
    -- Therefore, ‖z‖ = 2*√5 holds
    simp_all
  · -- m = -1 obviously doesn't satisfy the problem conditions
    have _ : m = -1 := by linarith
    linarith
