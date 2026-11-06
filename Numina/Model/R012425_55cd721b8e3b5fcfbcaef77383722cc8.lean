import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327302 {f : ℝ → ℝ} (hf : f = λ x => abs (sin (2 * x) + cos (2 * x))) :
    IsLeast {x | 0 < x ∧ f = λ y => f (y + x)} (π / 2) := by
  constructor
  · -- Show π / 2 is in the set
    constructor
    · -- Show π / 2 > 0
      linarith [Real.pi_pos]
    · -- Show f = fun y => f (y + π / 2)
      funext y
      have h1 : f y = abs (sin (2 * y) + cos (2 * y)) := by 
        simp [hf]
      have h2 : f (y + π / 2) = abs (sin (2 * (y + π / 2)) + cos (2 * (y + π / 2))) := by 
        simp [hf]
      have h3 : sin (2 * (y + π / 2)) = - sin (2 * y) := by 
        have h1 : sin (2 * (y + π / 2)) = sin (2 * y + π) := by ring_nf
        rw [h1]
        rw [sin_add, sin_pi, cos_pi]
        ring
      have h4 : cos (2 * (y + π / 2)) = - cos (2 * y) := by 
        have h1 : cos (2 * (y + π / 2)) = cos (2 * y + π) := by ring_nf
        rw [h1]
        rw [cos_add, sin_pi, cos_pi]
        ring
      rw [h1, h2, h3, h4]
      have h5 : abs (sin (2 * y) + cos (2 * y)) = abs (- sin (2 * y) - cos (2 * y)) := by 
        have h6 : sin (2 * y) + cos (2 * y) = - (- sin (2 * y) - cos (2 * y)) := by ring
        rw [h6]
        rw [abs_neg]
      exact h5
  · -- Show that π / 2 is the smallest positive period
    intro x hx
    rcases hx with ⟨hx_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h3 : ∀ y, f y = f (y + x) := by 
      intro y 
      apply congr_fun h_eq y
    have eq := h3 (π / 4 - x / 2)
    have eq1 : f (π / 4 - x / 2) = abs (sin (2 * (π / 4 - x / 2)) + cos (2 * (π / 4 - x / 2))) := by 
      simp [hf]
    have eq2 : f (π / 4 - x / 2 + x) = abs (sin (2 * (π / 4 - x / 2 + x)) + cos (2 * (π / 4 - x / 2 + x))) := by 
      simp [hf]
    rw [eq1, eq2] at eq 
    have eq3 : sin (2 * (π / 4 - x / 2)) + cos (2 * (π / 4 - x / 2)) = sin (π / 2 - x) + cos (π / 2 - x) := by 
      have h1 : 2 * (π / 4 - x / 2) = π / 2 - x := by ring
      rw [h1]
    have eq4 : sin (2 * (π / 4 - x / 2 + x)) + cos (2 * (π / 4 - x / 2 + x)) = sin (π / 2 + x) + cos (π / 2 + x) := by 
      have h1 : 2 * (π / 4 - x / 2 + x) = π / 2 + x := by ring
      rw [h1]
    have eq5 : abs (sin (2 * (π / 4 - x / 2)) + cos (2 * (π / 4 - x / 2))) = abs (sin (2 * (π / 4 - x / 2 + x)) + cos (2 * (π / 4 - x / 2 + x))) := by 
      simpa using eq 
    rw [eq3, eq4] at eq5
    have eq6 : sin (π / 2 - x) + cos (π / 2 - x) = cos x + sin x := by
      rw [sin_pi_div_two_sub, cos_pi_div_two_sub]
    have eq7 : sin (π / 2 + x) + cos (π / 2 + x) = cos x - sin x := by 
      rw [sin_add, cos_add, sin_pi_div_two, cos_pi_div_two]
      ring
    rw [eq6, eq7] at eq5
    have eq8 : (cos x + sin x) ^ 2 = (cos x - sin x) ^ 2 := by 
      have h1 : abs (cos x + sin x) = abs (cos x - sin x) := by 
        simpa using eq5 
      cases abs_cases (cos x + sin x) with
      | inl h2 =>
        cases abs_cases (cos x - sin x) with
        | inl h3 =>
          nlinarith 
        | inr h3 =>
          nlinarith 
      | inr h2 =>
        cases abs_cases (cos x - sin x) with
        | inl h3 =>
          nlinarith 
        | inr h3 =>
          nlinarith
    have eq9 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have eq10 : sin x * cos x = 0 := by 
      nlinarith 
    cases (mul_eq_zero.mp eq10) with 
    | inl h11 =>
      have h12 : sin x > 0 := by 
        apply sin_pos_of_pos_of_lt_pi
        linarith
        linarith [show x < Real.pi by linarith]
      linarith
    | inr h12 =>
      have h13 : cos x > 0 := by 
        apply cos_pos_of_mem_Ioo
        constructor
        linarith 
        linarith 
      linarith