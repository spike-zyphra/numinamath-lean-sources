import Mathlib

open BigOperators Real Set

theorem algebra_8993 (a : ℝ) (ha : a > -π) :
    MonotoneOn cos (Icc (-π) a) ↔ a ∈ Ioc (-π) 0 := by
  constructor
  · -- Assume cos is monotone on the interval, prove a ∈ (-π, 0].
    intro h
    have ha1 : a ≤ 0 := by
      by_contra h1
      push_neg at h1
      have ha2 : 0 ∈ Icc (-π) a := by
        constructor
        · linarith [Real.pi_pos, ha, h1]
        · linarith [Real.pi_pos, ha, h1]
      have h3 : (0 : ℝ) < min a (Real.pi / 2) := by
        have h4 : min a (Real.pi / 2) > (0 : ℝ) := by
          cases min_cases a (Real.pi / 2) with
          | inl h =>
            linarith
          | inr h =>
            have h5 : Real.pi / 2 > 0 := by
              linarith [Real.pi_pos]
            linarith
        linarith
      have h4 : min a (Real.pi / 2) ∈ Icc (-π) a := by
        constructor
        · -- Show that -π ≤ min a (Real.pi / 2)
          have h5 : -π < min a (Real.pi / 2) := by
            cases min_cases a (Real.pi / 2) with
            | inl h =>
              have h7 : a > (0 : ℝ) := by linarith
              nlinarith [Real.pi_pos]
            | inr h =>
              have h9 : Real.pi / 2 > (0 : ℝ) := by linarith [Real.pi_pos]
              nlinarith [Real.pi_pos]
          linarith
        · -- Show that min a (Real.pi / 2) ≤ a
          cases min_cases a (Real.pi / 2) with
          | inl h => linarith
          | inr h => linarith
      have h10 : cos (0 : ℝ) ≤ cos (min a (Real.pi / 2) : ℝ) := by
        apply h
        all_goals
        try { exact ha2 }
        try { exact h4  }
        all_goals
        try { 
          have h11 : (0 : ℝ) ≤ min a (Real.pi / 2) := by
            linarith [h3]
          linarith 
        }
      have h11 : cos (0 : ℝ) = 1 := Real.cos_zero
      have h12 : cos (min a (Real.pi / 2) : ℝ) < (1 : ℝ) := by
        have h13 : min a (Real.pi / 2) > 0 := h3
        have h14 : cos (min a (Real.pi / 2) : ℝ) < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals
            try { 
              nlinarith [Real.pi_pos, show min a (Real.pi / 2) ≤ Real.pi by
                cases min_cases a (Real.pi / 2) with
                | inl h =>
                  nlinarith [Real.pi_pos, Real.pi_gt_three]
                | inr h =>
                  nlinarith [Real.pi_pos, Real.pi_gt_three]
              ]
            }
        rw [Real.cos_zero] at h14
        linarith
      linarith [h10, h11, h12]
    constructor
    · -- Show that -π < a
      linarith [ha]
    · -- Show that a ≤ 0
      linarith [ha1]
  · -- Assume a ∈ (-π, 0], prove that cos is increasing on the interval.
    rintro ⟨ha1, ha2⟩
    intro x hx y hy hxy
    have h1 : -π ≤ x := by
      have h1 : x ∈ Icc (-π) a := hx
      exact h1.1
    have h2 : x ≤ a := by
      have h2 : x ∈ Icc (-π) a := hx
      exact h2.2
    have h3 : -π ≤ y := by
      have h3 : y ∈ Icc (-π) a := hy
      exact h3.1
    have h4 : y ≤ a := by
      have h4 : y ∈ Icc (-π) a := hy
      exact h4.2
    have h5 : x ≤ y := hxy
    have h6 : cos x ≤ cos y := by
      have h14 : -π ≤ x := h1
      have h15 : x ≤ y := h5
      have h16 : y ≤ 0 := by
        nlinarith
      have h17 : cos x ≤ cos y := by
        have h18 : x + Real.pi ≥ 0 := by nlinarith [Real.pi_pos, h1]
        have h19 : y + Real.pi ≥ 0 := by nlinarith [Real.pi_pos, h3]
        have h20 : x + Real.pi ≤ y + Real.pi := by linarith
        have h21 : (x + Real.pi) ≤ Real.pi := by
          nlinarith [Real.pi_pos, show a ≤ 0 by linarith [ha2]]
        have h22 : (y + Real.pi) ≤ Real.pi := by
          nlinarith [Real.pi_pos, show a ≤ 0 by linarith [ha2]]
        have h23 : cos (x + Real.pi) ≥ cos (y + Real.pi) := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          all_goals
            nlinarith
        have h24 : cos (x + Real.pi) = -cos x := by
          rw [Real.cos_add_pi]
        have h25 : cos (y + Real.pi) = -cos y := by
          rw [Real.cos_add_pi]
        nlinarith
      linarith
    linarith