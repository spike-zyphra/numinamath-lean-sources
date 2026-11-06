import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_221118 {f : ℝ → ℝ} (hf : f = λ x => abs (sin x) - abs (cos x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
  constructor 
  · -- Show that π is indeed a positive period of f
    constructor
    · -- Show that π is positive
      linarith [Real.pi_pos]
    · -- Show that f(x) = f(x + π) for all x
      funext x
      rw [hf]
      have h1 : sin (x + Real.pi) = - sin x := by 
        rw [sin_add_pi]
      have h2 : cos (x + Real.pi) = - cos x := by
        rw [cos_add_pi]
      simp [h1, h2]
      <;> ring_nf <;> norm_num
  · -- Show that π is the least positive period
    intro T ⟨hTpos, hT⟩
    by_contra h
    push_neg at h
    have h1 : ∀ x, f x = f (x + T) := by
      intro x
      simpa using congr_fun hT x
    -- Let's consider x = 0
    have eq1 := h1 0
    -- Let's consider x = π/2
    have eq2 := h1 (Real.pi / 2)
    -- Let's consider x = π/2 - T
    have eq3 := h1 (Real.pi / 2 - T)
    -- Let's consider x = π/4
    have eq4 := h1 (Real.pi / 4)
    -- Let's consider x = π - T/2
    have eq5 := h1 (Real.pi - T / 2)
    by_cases h11 : T ≤ Real.pi / 2
    · -- Case 1: 0 < T ≤ π/2
      have h12 : cos T ≥ 0 := by
        apply cos_nonneg_of_neg_pi_div_two_le_of_le
        all_goals nlinarith [Real.pi_gt_three, hTpos, h11]
      have h10 : sin T > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith
        linarith [h11, Real.pi_gt_three]
      have eq1' := h1 0
      simp [hf] at eq1' 
      have h42 : abs (sin T) = sin T := by
        rw [abs_of_nonneg (show sin T ≥ 0 by linarith)]
      have h43 : abs (cos T) = cos T := by
        rw [abs_of_nonneg (show cos T ≥ 0 by linarith)]
      rw [h42, h43] at eq1'
      -- Let's consider x = π/2
      have eq2 := h1 (Real.pi / 2)
      have eq2_lhs : f (Real.pi / 2) = 1 := by
        simp [hf, sin_pi_div_two, cos_pi_div_two]
        <;> norm_num
      have eq2_rhs : f (Real.pi / 2 + T) = abs (sin (Real.pi / 2 + T)) - abs (cos (Real.pi / 2 + T)) := by
        simp [hf]
      rw [eq2_lhs, eq2_rhs] at eq2
      have h44 : sin (Real.pi / 2 + T) = cos T := by
        rw [sin_add]
        simp [cos_pi_div_two, sin_pi_div_two]
        <;> ring_nf <;> simp [sin_sq]
        <;> nlinarith
      have h45 : cos (Real.pi / 2 + T) = -sin T := by
        rw [cos_add]
        simp [cos_pi_div_two, sin_pi_div_two]
        <;> ring_nf <;> simp [sin_sq]
        <;> nlinarith
      rw [h44, h45] at eq2
      rw [abs_neg] at eq2
      rw [abs_of_nonneg (show cos T ≥ 0 by linarith)] at eq2
      rw [abs_of_nonneg (show sin T ≥ 0 by linarith)] at eq2
      all_goals
        try { 
          nlinarith [Real.sin_sq_add_cos_sq T, sq_nonneg (T - 0), Real.pi_pos, Real.pi_gt_three, sq_nonneg (sin T - cos T)]
        }
        try { 
          have h21 : sin T ^ 2 + cos T ^ 2 = 1 := by
            exact Real.sin_sq_add_cos_sq T
          nlinarith [h21, sq_nonneg (T - Real.pi / 2), sq_nonneg (sin T - cos T), sq_nonneg (sin T ^ 2 - cos T ^ 2)]
        }
    · -- Case 2: π/2 < T < π
      have h12 : cos T < 0 := by
        apply cos_neg_of_pi_div_two_lt_of_lt
        all_goals linarith [Real.pi_gt_three, hTpos, h]
      have h10 : sin T > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith
        linarith [h, Real.pi_gt_three]
      have eq1' := h1 0
      simp [hf] at eq1' 
      have h42 : abs (sin T) = sin T := by
        rw [abs_of_nonneg (show sin T ≥ 0 by linarith)]
      have h43 : abs (cos T) = -cos T := by
        rw [abs_of_neg (show cos T < 0 by linarith)]
      rw [h42, h43] at eq1'
      -- Let's consider x = π/2
      have eq2 := h1 (Real.pi / 2)
      have eq2_lhs : f (Real.pi / 2) = 1 := by
        simp [hf, sin_pi_div_two, cos_pi_div_two]
        <;> norm_num
      have eq2_rhs : f (Real.pi / 2 + T) = abs (sin (Real.pi / 2 + T)) - abs (cos (Real.pi / 2 + T)) := by
        simp [hf]
      rw [eq2_lhs, eq2_rhs] at eq2
      have h44 : sin (Real.pi / 2 + T) = cos T := by
        rw [sin_add]
        simp [cos_pi_div_two, sin_pi_div_two]
        <;> ring_nf <;> simp [sin_sq]
        <;> nlinarith
      have h45 : cos (Real.pi / 2 + T) = -sin T := by
        rw [cos_add]
        simp [cos_pi_div_two, sin_pi_div_two]
        <;> ring_nf <;> simp [sin_sq]
        <;> nlinarith
      rw [h44, h45] at eq2
      rw [abs_neg] at eq2
      rw [abs_of_nonneg (show sin T ≥ 0 by linarith)] at eq2
      rw [abs_of_neg (show cos T < 0 by linarith)] at eq2
      all_goals
        try { 
          nlinarith [Real.sin_sq_add_cos_sq T, sq_nonneg (T - 0), Real.pi_pos, Real.pi_gt_three, sq_nonneg (sin T - cos T)]
        }
        try { 
          have h21 : sin T ^ 2 + cos T ^ 2 = 1 := by
            exact Real.sin_sq_add_cos_sq T
          nlinarith [h21, sq_nonneg (T - Real.pi / 2), sq_nonneg (sin T - cos T), sq_nonneg (sin T ^ 2 - cos T ^ 2)]
        }