import Mathlib

open Set

theorem algebra_9312 {f : ℝ → ℝ} (hf : ∀ x, f x = - f (-x)) (hinc : StrictMonoOn f (Set.Ioi 0))
    (h2 : f (-2) = 0) :
    {x | x * f x < 0} = Set.Ioo (-2) 0 ∪ Set.Ioo 0 2 := by

  have h2' : f 2 = 0 := by
    have h21 : f 2 = - f (-2) := hf 2
    rw [h2] at h21
    linarith

  have h5 : ∀ x, 0 < x → x < 2 → f x < 0 := by
    intro x hx1 hx2
    have hx3 : x ∈ Set.Ioi (0 : ℝ) := by
      simp at *
      all_goals linarith
    have h211 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      simp at *
      all_goals linarith
    have h7 : f x < f (2 : ℝ) := by
      apply hinc
      all_goals
      try { tauto }
      all_goals
      try { linarith }
    linarith [h2', h7]

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo]
  constructor
  · -- Assume x * f x < 0, prove (x ∈ (-2,0)) ∨ (x ∈ (0,2))
    intro h
    by_cases h7 : x > 0
    · -- If x > 0, then f x < 0
      have h8 : f x < 0 := by nlinarith
      have h9 : x < 2 := by
        by_contra h9
        push_neg at h9
        have h10 : f x ≥ 0 := by
          by_cases h10 : x > (2 : ℝ)
          · -- If x > 2, then since f is strictly increasing on (0, +infty) and f 2 = 0, we have f x > 0
            have h11 : f 2 < f x := by
              apply hinc
              all_goals
              try { simp; all_goals linarith }
              all_goals
              try { nlinarith }
            linarith [h2']
          · -- x = 2
            have h12 : x = (2 : ℝ) := by linarith
            rw [h12]
            linarith [h2']
        linarith
      right
      constructor <;> linarith
    · -- x ≤ 0
      by_cases h8 : x = 0
      · -- x = 0, but x * f x = 0, contradict
        rw [h8] at h
        norm_num at h
      · -- x < 0
        have h9 : x < 0 := by
          by_contra h9
          push_neg at h9
          have h70 : x = 0 := by linarith
          tauto
        have h10 : f x > 0 := by nlinarith
        have h11 : x > -2 := by
          by_contra h11
          push_neg at h11
          have h12 : f x ≤ 0 := by
            have h13 : -x ≥ (2 : ℝ) := by nlinarith
            have h14 : f (-x) ≥ 0 := by
              by_cases h15 : -x > (2 : ℝ)
              · -- If -x > 2, then f (-x) > 0
                have h16 : f 2 < f (-x) := by
                  apply hinc
                  all_goals
                  try { simp; all_goals nlinarith }
                  all_goals
                  try { nlinarith }
                linarith [h2']
              · -- -x = 2
                have h18 : -x = (2 : ℝ) := by linarith
                rw [h18]
                linarith [h2']
            have h17 : f x = - f (-x) := by
              have h171 : f x = - f (-x) := hf x
              linarith
            linarith
          linarith
        left
        constructor <;> linarith
  · -- Assume (x ∈ (-2,0)) ∨ (x ∈ (0,2)), prove x * f x < 0
    rintro (h | h)
    · -- x ∈ (-2, 0)
      rcases h with ⟨h11, h12⟩
      have h13 : 0 < -x := by nlinarith
      have h14 : -x < 2 := by nlinarith
      have h15 : f (-x) < 0 := h5 (-x) h13 h14
      have hfx : f x > 0 := by
        have h91 : f x = - f (-x) := hf x
        nlinarith
      nlinarith
    · -- x ∈ (0, 2)
      rcases h with ⟨h11, h12  ⟩
      have h13 : 0 < x := h11
      have h14 : x < 2 := h12
      have h15 : f x < 0 := h5 x h13 h14
      nlinarith