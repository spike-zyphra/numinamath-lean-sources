import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22760 {f : ℝ → ℝ} (hf : f = λ x => cos (sin x)) :
    IsLeast {T | 0 < T ∧ Function.Periodic f T} (Real.pi) := by
  constructor
  · -- Show that π is in the set, by proving it's a positive period of f
    constructor
    · -- Show that π is positive
      exact Real.pi_pos
    · -- Show that f is periodic with period π
      rw [hf]
      intro x
      have h1 : sin (x + Real.pi) = -sin x := Real.sin_add_pi x
      have h2 : cos (sin (x + Real.pi)) = cos (sin x) := by
        rw [show sin (x + Real.pi) = - sin x by linarith [h1]]
        have h3 : cos (- sin x) = cos (sin x) := by
          rw [show - sin x = - (sin x) by ring]
          rw [cos_neg]
        exact h3
      simpa using h2
  · -- Show that π is the least element of the set
    intro T ⟨hTpos, hTperiod⟩
    have h1 : ∀ x, f (x + T) = f x := by
      simpa using hTperiod
    have h2 := h1 0
    rw [hf] at h2
    simp at h2
    have h3 : cos (sin T) = 1 := by linarith
    have h4 : sin T = 0 := by
      rw [Real.cos_eq_one_iff] at h3
      rcases h3 with ⟨n, hn⟩
      have h7 : -1 ≤ sin T := by 
        apply neg_one_le_sin
      have h8 : sin T ≤ 1 := by
        apply sin_le_one
      have h9 : n = 0 := by
        by_cases h : n > 0
        · -- Assume n > 0
          have hn1 : n ≥ 1 := by omega
          have hn2 : (n : ℝ) ≥ 1 := by exact_mod_cast hn1
          nlinarith [Real.pi_pos, Real.pi_gt_three, show sin T ≤ 1 by apply sin_le_one]
        by_cases h' : n < 0
        · -- Assume n < 0
          have hn1 : n ≤ -1 := by omega
          have hn2 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hn1
          nlinarith [Real.pi_pos, Real.pi_gt_three, show -1 ≤ sin T by apply neg_one_le_sin]
        omega
      have h9' : (n : ℝ) = (0 : ℝ) := by
        exact_mod_cast h9
      rw [h9'] at hn
      linarith
    by_contra h
    push_neg at h
    have h11 : T > 0 := hTpos
    have h12 : T < Real.pi := h
    have h13 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals nlinarith [Real.pi_gt_three, h11, h12]
    linarith [h13, h4]