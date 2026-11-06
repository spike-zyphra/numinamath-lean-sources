import Mathlib

open Real

/- 3. Given the function $f(x)=\sin \omega x+\cos \omega x(\omega>0), x \in \mathbf{R}$, if the function $f(x)$ is monotonically increasing in the interval $(-\omega, \omega)$, and the graph of the function $y=f(x)$ is symmetric about the line $x=\omega$, then the value of $\omega$ is -/
theorem algebra_283209 (ω : ℝ) (hω : ω > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin (ω * x) + Real.cos (ω * x))
    (hinc : ∀ x ∈ Set.Ioo (-ω) ω, deriv f x ≥ 0)
    (hsymm : ∀ x, f (ω - x) = f (ω + x)) :
    ω = Real.sqrt Real.pi / 2 := by
  -- We have f(x) = √2 * sin (ω * x + π / 4).
  have heq x : f x = √2 * sin (ω * x + π / 4) := by
    rw [sin_add, cos_pi_div_four, sin_pi_div_four, hf]
    ring_nf
    simp
  -- Prove that there exists a natural number k such that
  -- ω ^ 2 = k * π + π / 4.
  have ⟨k, hk⟩ : ∃ k : ℕ, ω ^ 2 = k * π + π / 4 := by
    -- The condition f (ω - x) = f (ω + x) implies that
    -- sin (ω * (ω - x) + π / 4) = sin (ω * (ω + x) + π / 4).
    -- This equation has the following solutions:
    -- ω * x * 2 - π * ↑k * 2 = 0 ∨ ω ^ 2 * 2 + (π * (-1 / 2) - π * ↑k * 2) = 0
    -- where k ∈ ℤ (and k depends on the choice of x).
    simp [heq, sin_eq_sin_iff] at hsymm
    simp [← sub_eq_zero] at hsymm
    ring_nf at hsymm
    -- It is enough to show that ω ^ 2 * 2 + (π * (-1 / 2) - π * ↑k * 2) = 0.
    suffices h : ∃ k : ℤ, ω ^ 2 * 2 + (π * (-1 / 2) - π * ↑k * 2) = 0 by
      have ⟨k, hk⟩ := h
      -- We have 0 ≤ k because ω > 0.
      have hk0 : 0 ≤ k := by
        contrapose! hk
        replace hk : k ≤ -1 := by linarith
        rify at hk
        nlinarith [pi_pos]
      lift k to ℕ using hk0
      use k
      linear_combination hk / 2
    -- Show that the case ω * x * 2 - π * ↑k * 2 = 0 is impossible.
    -- Let x = π and find k such that ω * π * 2 - π * ↑k * 2 = 0, i.e., ω = k.
    have ⟨k, hk⟩ := hsymm π
    -- Let x = 1 and find k' such that ω * 1 * 2 - π * k' * 2 = 0, i.e., ω = π * k'.
    have ⟨k', hk'⟩ := hsymm 1
    cases' hk with hk hk <;> [skip; use k]
    cases' hk' with hk' hk' <;> [skip; use k']
    replace hk : ω = k := by nlinarith [pi_pos]
    replace hk' : ω = π * k' := by linarith
    -- We get π * k' = k for k', k ∈ ℤ.
    rw [hk'] at hk
    -- This equality implies that k' = 0 (because π * k' is irrational for all k' ≠ 0).
    apply_fun Irrational at hk
    -- k' = 0 implies that ω = π * k' = 0, a contradiction with ω > 0.
    simp at hk
    simp [hk] at hk'
    linarith
  -- Prove that ω ≤ π / 2.
  have hω2 : ω ≤ π / 2 := by
    -- Suppose that π / 2 < ω and show that the derivative
    -- of f(x) is negative at some point in (-ω, ω).
    contrapose! hinc
    -- Let x = π / 2 / ω.
    use (π / 2) / ω
    simp only [Set.mem_Ioo]
    constructorm* _ ∧ _
    -- Show that -ω < x. It follows from -ω < 0 < x.
    · rw [← sub_pos]
      simp
      positivity
    -- Show that x < ω. It follows from x < 1 < ω (since ω > π / 2).
    · suffices π / 2 / ω < 1 by linarith [pi_gt_d2]
      rwa [div_lt_one hω]
    -- Find the derivative of f(x).
    rw [show f = (fun x => f x) by simp]
    simp [heq]
    rw [deriv_sin (by fun_prop), deriv_add_const, deriv_const_mul _ (by fun_prop), deriv_id'', mul_one]
    -- We have f'(x) = √2 * (cos (ω * (π / 2 / ω) + π / 4) * ω).
    -- We need to show that f'(x) < 0.
    -- We get f'(x) = √2 * (-sin (π / 4) * ω) = √2 * -√2 / 2 * ω < 0.
    rw [show ω * (π / 2 / ω) = π / 2 by field_simp; ring, add_comm]
    rw [cos_add_pi_div_two, sin_pi_div_four]
    ring_nf
    simp
    linarith
  -- It is enough to show that k = 0.
  suffices k = 0 by
    -- If k = 0 then ω^2 = π / 4.
    simp [this] at hk
    -- 0 < ω implies ω = √π / 2.
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    rw [div_pow, sq_sqrt (by positivity)]
    linarith
  -- Suppose that k ≠ 0 and show that ω^2 < k * π + π / 4.
  contrapose! hk
  apply ne_of_lt
  calc
    -- We have ω^2 ≤ (π / 2)^2 (since 0 < ω ≤ π / 2).
    ω^2 ≤ (π / 2)^2 := by
      rw [sq_le_sq₀ (by positivity) (by positivity)]
      exact hω2
    -- (π / 2)^2 < π + π / 4.
    _ < π + π / 4 := by nlinarith [pi_lt_d2]
    -- k ≠ 0 implies that 1 ≤ k, so
    -- π + π / 4 ≤ k * π + π / 4.
    _ ≤ k * π + π / 4 := by
      replace hk : 1 ≤ k := by omega
      rify at hk
      nlinarith