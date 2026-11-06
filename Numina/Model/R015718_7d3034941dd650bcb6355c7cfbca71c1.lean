import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12711 {f : ℝ → ℝ} (hf : f = λ x => -log (abs (sin x))) :
    Function.Periodic f π ∧ MonotoneOn (-f) (Set.Ioo 0 (π/2)) ∧ Even (-f) := by
  constructor
  · -- Verify f is π-periodic
    rw [hf]
    unfold Function.Periodic
    intro x
    have h1 : abs (sin (x + π)) = abs (sin x) := by
      have h2 : sin (x + π) = - sin x := by
        rw [sin_add, sin_pi, cos_pi]
        ring
      rw [h2]
      rw [abs_neg]
    simp [h1]
    all_goals try { norm_num }
    all_goals try { tauto }
  constructor
  · -- Verify -f is monotone on (0, π/2)
    rw [hf]
    intro x hx y hy hxy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h2 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h3 : sin y > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h4 : abs (sin x) = sin x := by
      rw [abs_of_pos h2]
    have h5 : abs (sin y) = sin y := by
      rw [abs_of_pos h3]
    have h6 : sin x ≤ sin y := by
      have h8 : x ≤ y := hxy
      have h9 : sin x ≤ sin y := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      assumption
    have h7 : log (abs (sin x)) = log (sin x) := by
      rw [h4]
    have h7' : log (abs (sin y)) = log (sin y) := by
      rw [h5]
    have h8 : log (sin x) ≤ log (sin y) := by
      apply Real.log_le_log
      all_goals linarith
    simp_all
    all_goals try { linarith [h8, h7, h7'] }
    all_goals try { linarith [h7, h7'] }
  · -- Verify -f is even
    unfold Even
    rw [hf]
    use (fun x => (log (abs (sin x))) / 2)
    funext
    simp [hf]
    <;> try { simp [abs_neg, Real.sin_neg] }
    <;> try { tauto }
    <;> try { 
      linarith [Real.sin_sq_add_cos_sq]
    }