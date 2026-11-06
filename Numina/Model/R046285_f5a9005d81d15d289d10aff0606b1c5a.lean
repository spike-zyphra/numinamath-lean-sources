import Mathlib
open Real Set
open scoped BigOperators

theorem algebra_9367_1 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x ^ 2 + cos (2 * x - π / 3)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} π := by
  -- Rewrite the expression of f(x).
  have f_eq : ∀ x, f x = 1 + sin (x * 2 + π * (-1 / 6)) := by
    conv at hf =>
      rhs
      ext x -- Dealing with 2 * sin x ^ 2 + cos (2 * x - π / 3).
      rw [sin_sq_eq_half_sub]
      ring_nf
      rw [(by ring : 1 - cos (x * 2) + cos (x * 2 + π * (-1 / 3)) = 1 + (cos (x * 2 + π * (-1 / 3)) - cos (x * 2)))]
      congr
      . skip
      . -- Dealing with cos (2 * x - π / 3) - cos (x * 2).
        rw [cos_sub_cos] -- Use the sum to product formula of cos.
        ring_nf
        congr
        congr
        . congr
          . skip
          . rw [(by ring_nf : sin (π * (-1 / 6)) = sin (-(π / 6))), sin_neg, sin_pi_div_six]
        . skip
    simp at hf
    intro x
    rw [hf]
  clear hf
  -- Break into two goals:
  -- (1) π is a period.
  -- (2) There is no smaller period.
  constructor <;> simp [lowerBounds]
  . refine ⟨pi_pos, ?_⟩
    -- Prove that f(x) = f(x + π).
    ext x
    rw [f_eq, f_eq]
    ring_nf
    conv =>
      lhs
      rw [<-sin_add_two_pi]
    ring_nf
  . intro T T_pos T_period
    -- Prove that T ≥ π if f(x) = f(x + T) for all x and positive T > 0.
    have h : ∀ x, f x = f (x + T) := by
      intro x
      tauto
    specialize h (π / 3) -- Let x = π / 3, so that sin (2 * x - π / 6) = 1.
    simp [f_eq, f_eq] at h
    conv at h =>
      lhs
      rw [(by ring : π / 3 * 2 + π * (-1 / 6) = π / 2)]
    rw [sin_pi_div_two] at h
    symm at h
    rw [sin_eq_one_iff] at h -- From equation of the form 1 = sin x, we can obtain x = 2kπ.
    obtain ⟨k, hk⟩ := h
    replace hk : T = k * π := by linarith
    rw [hk] at T_pos ⊢
    replace T_pos : (0 : ℝ) < k := by nlinarith [pi_pos]
    replace T_pos : 0 < k := Int.cast_pos.1 T_pos
    replace T_pos : (1 : ℝ) ≤ k := Int.cast_one_le_of_pos T_pos
    nlinarith [pi_pos]

theorem algebra_9367_2 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x ^ 2 + cos (2 * x - π / 3)):
    MonotoneOn f (Ioc 0 (π / 3)) := by
  have f_eq : ∀ x, f x = 1 + sin (x * 2 + π * (-1 / 6)) := by
    conv at hf =>
      rhs
      ext x -- Dealing with 2 * sin x ^ 2 + cos (2 * x - π / 3).
      rw [sin_sq_eq_half_sub]
      ring_nf
      rw [(by ring : 1 - cos (x * 2) + cos (x * 2 + π * (-1 / 3)) = 1 + (cos (x * 2 + π * (-1 / 3)) - cos (x * 2)))]
      congr
      . skip
      . -- Dealing with cos (2 * x - π / 3) - cos (x * 2).
        rw [cos_sub_cos] -- Use the sum to product formula of cos.
        ring_nf
        congr
        congr
        . congr
          . skip
          . rw [(by ring_nf : sin (π * (-1 / 6)) = sin (-(π / 6))), sin_neg, sin_pi_div_six]
        . skip
    simp at hf
    intro x
    rw [hf]
  intro x hx y hy hxy
  simp at hx hy
  rw [f_eq, f_eq]
  have h1 : 0 < x := by linarith [hx.1]
  have h2 : x ≤ π / 3 := by linarith [hx.2]
  have h3 : 0 < y := by linarith [hy.1]
  have h4 : y ≤ π / 3 := by linarith [hy.2]
  have h5 : x ≤ y := hxy
  have h6 : x * 2 + π * (-1 / 6) ≤ y * 2 + π * (-1 / 6) := by
    nlinarith
  have h7 : -Real.pi / 2 ≤ x * 2 + Real.pi * (-1 / 6) := by
    nlinarith [pi_pos]
  have h8 : -Real.pi / 2 ≤ y * 2 + Real.pi * (-1 / 6) := by
    nlinarith [pi_pos]
  have h9 : x * 2 + Real.pi * (-1 / 6) ≤ Real.pi / 2 := by
    nlinarith [pi_pos]
  have h10 : y * 2 + Real.pi * (-1 / 6) ≤ Real.pi / 2 := by
    nlinarith [pi_pos]
  have h11 : sin (x * 2 + Real.pi * (-1 / 6)) ≤ sin (y * 2 + Real.pi * (-1 / 6)) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    all_goals
      nlinarith [pi_pos]
  linarith