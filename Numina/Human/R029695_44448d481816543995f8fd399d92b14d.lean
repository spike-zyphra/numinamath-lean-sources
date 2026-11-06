import Mathlib

/- Given the function y = sin(2x + φ) (- $$\frac {π}{2}＜$$$$φ＜ \frac {π}{2}$$), the maximum value is obtained at x = $$\frac {π}{6}$$. Find the value of φ.-/
theorem algebra_9228 (φ : ℝ) (hφ : -(Real.pi / 2) < φ ∧ φ < Real.pi / 2)
    (f : ℝ → ℝ) (hf : f = fun x => Real.sin (2 * x + φ))
    (h : IsGreatest (Set.range f) (f (Real.pi / 6))) :
    φ = Real.pi / 6 := by
  -- It's clear that $f(\pi/6)=1$.
  have : f (Real.pi / 6) = 1 := by
    apply le_antisymm
    . simp [hf]
      exact (Real.sin_mem_Icc _).2
    apply h.2
    use (Real.pi / 2 - φ) / 2
    simp [hf]
    ring_nf
    nth_rw 2 [← Real.sin_pi_div_two]
    congr
    norm_num
  -- Since $f(\pi/6)=1$ we have $\pi / 2 + 2k\pi) = 2 * (\pi / 6) + φ$.
  simp [hf] at this
  rw [Real.sin_eq_one_iff] at this
  rcases this with ⟨k, hk⟩
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  -- If k < 0, then φ cannot lie in $(-\pi/2, \pi/2)$.
  . have : k ≤ -1 := by omega
    rify at this
    have : (k : ℝ) * (2 * Real.pi) ≤ (-1) * (2 * Real.pi) := by nlinarith
    have : 2 * (Real.pi / 6) + φ ≤ Real.pi / 2 + (-1) * (2 * Real.pi) := by linarith
    linarith
  -- If k = 0, then φ equals to $\pi/6$.
  . rw [hk0] at hk
    norm_num at hk
    linarith
  -- If k > 0, then φ cannot lie in $(-\pi/2, \pi/2)$.
  change 1 ≤ k at hk0
  rify at hk0
  have : 1 * (2 * Real.pi) ≤ (k : ℝ) * (2 * Real.pi) := by nlinarith
  have : Real.pi / 2 + 1 * (2 * Real.pi) ≤ 2 * (Real.pi / 6) + φ := by linarith
  linarith
