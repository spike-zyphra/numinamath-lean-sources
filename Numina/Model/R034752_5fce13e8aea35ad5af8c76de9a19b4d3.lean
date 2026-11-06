import Mathlib

open BigOperators Real Set

theorem algebra_320318 {f g : ℝ → ℝ}
  (hf : f = λ x => π - arcsin (3 - x)) (hg : g = λ x => 3 - sin x)
  (x : ℝ) (hx : 2 ≤ x ∧ x ≤ 4) :
  g (f x) = x ∧ f (g x) = x := by
  have h1 : 2 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  have h3 : -1 ≤ 3 - x ∧ 3 - x ≤ 1 := by
    constructor
    · linarith
    · linarith
  have h4 : g (f x) = x := by
    rw [hg, hf]
    have h5 : 3 - sin (π - arcsin (3 - x)) = x := by
      have h6 : sin (π - arcsin (3 - x)) = 3 - x := by
        have h7 : sin (π - arcsin (3 - x)) = sin (arcsin (3 - x)) := by
          rw [sin_pi_sub]
        rw [h7]
        have h10 : sin (arcsin (3 - x)) = 3 - x := by
          apply Real.sin_arcsin
          all_goals
            linarith [h3.1, h3.2]
        rw [h10]
      nlinarith
    simp at h5 ⊢
    all_goals linarith
  have h11 : f (g x) = x := by
    rw [hg, hf]
    have h100 : π - arcsin (3 - (3 - sin x)) = x := by
      have h7 : arcsin (3 - (3 - sin x)) = arcsin (sin x) := by
        have h8 : 3 - (3 - sin x) = sin x := by ring
        rw [h8]
      rw [h7]
      have h12 : arcsin (sin x) = π - x := by
        have h14 : arcsin (sin x) = π - x := by
          have h17 : arcsin (sin x) = arcsin (sin (π - x)) := by
            have h80 : sin x = sin (π - x) := by 
              rw [sin_pi_sub]
            rw [h80]
          have h170 : arcsin (sin (π - x)) = π - x := by
            have h33 : -(Real.pi / 2) ≤ π - x := by
              nlinarith [Real.pi_lt_31416, Real.pi_gt_three]
            have h22 : π - x ≤ Real.pi / 2 := by
              nlinarith [Real.pi_lt_31416, Real.pi_gt_three]
            apply Real.arcsin_sin
            all_goals
              nlinarith [Real.pi_lt_31416, Real.pi_gt_three]
          rw [h17, h170]
        linarith
      linarith
    simp at h100 ⊢
    all_goals linarith
  constructor
  · exact h4
  · exact h11