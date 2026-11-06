import Mathlib

theorem algebra_515331 {f : ℝ → ℝ} (hf : f = fun x => (Real.cos x)^2) :
    IsLeast {T | 0 < T ∧ f = fun x => f (x + T)} (Real.pi) := by
  constructor
  · -- Show that π is indeed a positive period of f.
    constructor
    · -- Show that π > 0
      exact Real.pi_pos
    · -- Show that f(x) = f(x + π) for all x.
      funext x
      rw [hf]
      have h1 : Real.cos (x + Real.pi) = - Real.cos x := by 
        rw [Real.cos_add_pi]
      simp [h1]
  · -- Show that π is the smallest positive period.
    intro T ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    have eq1 := congr_fun h_eq (Real.pi / 2 - T)
    simp [hf] at eq1
    have h3 : Real.cos (Real.pi / 2 - T + T) = 0 := by
      have h4 : Real.pi / 2 - T + T = Real.pi / 2 := by 
        ring
      rw [h4]
      simp [Real.cos_pi_div_two]
    have h4 : Real.cos (Real.pi / 2 - T) = Real.sin T := by 
      rw [show Real.pi / 2 - T = Real.pi / 2 - T by rfl]
      rw [Real.cos_pi_div_two_sub]
    have h6 : Real.sin T ^ 2 = 0 := by
      nlinarith [h4, eq1, h3]
    have h7 : Real.sin T = 0 := by
      nlinarith
    have h8 : T > 0 := hT_pos 
    have h9 : T < Real.pi := by linarith [h]
    have h11 : Real.sin T > 0 := by 
      apply Real.sin_pos_of_pos_of_lt_pi 
      all_goals linarith 
    linarith [h7, h11]