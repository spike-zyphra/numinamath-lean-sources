import Mathlib
open Real Set
open scoped BigOperators

theorem algebra_9391 {f : ℝ → ℝ} (hf : f = λ x => 3 - 2 * sin x) :
    ∀ k : ℤ, MonotoneOn f {x | π / 2 + 2 * k * π ≤ x ∧ x ≤ 3 * π / 2 + 2 * k * π} := by 
  intro k 
  intro x hx y hy hxy
  simp at hx hy
  simp only [hf]
  obtain ⟨hx₁, hx₂⟩ := hx 
  obtain ⟨hy₁, hy₂⟩ := hy
  have h6 : π / 2 + 2 * k * π ≤ x := by 
    linarith 
  have h7 : x ≤ 3 * π / 2 + 2 * k * π := by 
    linarith 
  have h8 : π / 2 + 2 * k * π ≤ y := by 
    linarith 
  have h9 : y ≤ 3 * π / 2 + 2 * k * π := by 
    linarith 
  have h14 : sin x = sin (x - 2 * k * π) := by 
    rw [show x - 2 * k * π = x - k * (2 * π) by ring] 
    rw [sin_sub_int_mul_two_pi] 
  have h15 : sin y = sin (y - 2 * k * π) := by 
    rw [show y - 2 * k * π = y - k * (2 * π) by ring] 
    rw [sin_sub_int_mul_two_pi]
  have h10 : π / 2 ≤ x - 2 * k * π := by 
    linarith
  have h11 : x - 2 * k * π ≤ 3 * π / 2 := by 
    linarith 
  have h12 : π / 2 ≤ y - 2 * k * π := by 
    linarith
  have h13 : y - 2 * k * π ≤ 3 * π / 2 := by 
    linarith 
  have h17 : x - 2 * k * π ≤ y - 2 * k * π := by 
    linarith 
  have h3 : sin (x - 2 * k * π) ≥ sin (y - 2 * k * π) := by
    have h6' : sin (x - 2 * k * π) = sin (π - (x - 2 * k * π)) := by 
      rw [sin_pi_sub]
    have h7' : sin (y - 2 * k * π) = sin (π - (y - 2 * k * π)) := by 
      rw [sin_pi_sub]
    rw [h6', h7']
    have h91 : -Real.pi / 2 ≤ π - (y - 2 * k * π) := by 
      nlinarith [Real.pi_pos]
    have h81 : π - (y - 2 * k * π) ≤ Real.pi / 2 := by 
      nlinarith [Real.pi_pos]
    have h92 : -Real.pi / 2 ≤ π - (x - 2 * k * π) := by 
      nlinarith [Real.pi_pos]
    have h82 : π - (x - 2 * k * π) ≤ Real.pi / 2 := by 
      nlinarith [Real.pi_pos]
    have h101 : π - (y - 2 * k * π) ≤ π - (x - 2 * k * π) := by
      linarith 
    have h120 : sin (π - (x - 2 * k * π)) ≥ sin (π - (y - 2 * k * π)) := by 
      have h121 : sin (π - (x - 2 * k * π)) ≥ sin (π - (y - 2 * k * π)) := by 
        apply sin_le_sin_of_le_of_le_pi_div_two
        all_goals 
          nlinarith [Real.pi_pos]
      linarith
    linarith 
  have h30 : 3 - 2 * sin x ≤ 3 - 2 * sin y := by
    nlinarith
  exact h30