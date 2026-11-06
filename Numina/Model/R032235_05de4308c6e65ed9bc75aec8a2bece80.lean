import Mathlib

open Real Set
open scoped Real

theorem algebra_231211 (α β γ : Real) (h : α ∈ Ioo 0 π)
  (h' : β ∈ Ioo 0 π) (h'' : γ ∈ Ioo 0 π) (h''' : α + β + γ = π) :
  (sin β ^ 2 + sin γ ^ 2 - 2 * sin β * sin γ * cos α) / sin α ^ 2 =
  (sin α ^ 2 + sin γ ^ 2 - 2 * sin α * sin γ * cos β) / sin β ^ 2 ∧
  (sin α ^ 2 + sin β ^ 2 - 2 * sin α * sin β * cos γ) / sin γ ^ 2 =
  (sin β ^ 2 + sin γ ^ 2 - 2 * sin β * sin γ * cos α) / sin α ^ 2 := by
  rcases h with ⟨hα1, hα2⟩
  rcases h' with ⟨hβ1, hβ2⟩
  rcases h'' with ⟨hγ1, hγ2⟩
  have h1 : sin α > 0 := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith
  have h2 : sin β > 0 := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith
  have h3 : sin γ > 0 := by apply sin_pos_of_pos_of_lt_pi; linarith; linarith
  have eq1 : sin β ^ 2 + sin γ ^ 2 - 2 * sin β * sin γ * cos α = sin α ^ 2 := by
    have h4 : α = π - (β + γ) := by
      linarith 
    have h5 : cos α = - cos (β + γ) := by 
      rw [h4]
      have : cos (π - (β + γ)) = - cos (β + γ) := by
        rw [cos_pi_sub]
      linarith 
    have h6 : cos (β + γ) = cos β * cos γ - sin β * sin γ := by
      rw [cos_add]
    rw [h5, h6]
    have h7 : sin α = sin (β + γ) := by 
      have h8 : α = π - (β + γ) := by
        linarith 
      rw [h8]
      have h9 : sin (π - (β + γ)) = sin (β + γ) := by
        rw [sin_pi_sub]
      linarith 
    have h8 : sin (β + γ) = sin β * cos γ + cos β * sin γ := by 
      rw [sin_add]
    rw [h7, h8]
    <;> nlinarith [Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
  have eq2 : sin α ^ 2 + sin γ ^ 2 - 2 * sin α * sin γ * cos β = sin β ^ 2 := by 
    have h8 : β = π - (α + γ) := by
      linarith 
    have h9 : sin β = sin (α + γ) := by 
      have h10 : β = π - (α + γ) := by
        linarith
      rw [h10]
      have h11 : sin (π - (α + γ)) = sin (α + γ) := by
        rw [sin_pi_sub]
      linarith 
    have h10 : cos β = - cos (α + γ) := by 
      have h11 : β = π - (α + γ) := by
        linarith 
      rw [h11]
      have h12 : cos (π - (α + γ)) = - cos (α + γ) := by 
        rw [cos_pi_sub]
      linarith 
    have h11 : cos (α + γ) = cos α * cos γ - sin α * sin γ := by 
      rw [cos_add]
    rw [h9, h10, h11]
    have h12 : sin (α + γ) = sin α * cos γ + cos α * sin γ := by 
      rw [sin_add]
    rw [h12]
    <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq γ, mul_pos h1 h3, mul_pos h1 h2, mul_pos h3 h2]
  constructor 
  · -- Show that the first two expressions are equal
    have eq3 : (sin β ^ 2 + sin γ ^ 2 - 2 * sin β * sin γ * cos α) / sin α ^ 2 = (sin α ^ 2 + sin γ ^ 2 - 2 * sin α * sin γ * cos β) / sin β ^ 2 := by
      rw [eq1, eq2]
      <;> field_simp [show sin α ^ 2 > 0 by nlinarith [h1], show sin β ^ 2 > 0 by nlinarith [h2]]
      <;> nlinarith 
    exact eq3
  · -- Show that the third expression is equal to the first one
    have eq3 : (sin α ^ 2 + sin β ^ 2 - 2 * sin α * sin β * cos γ) / sin γ ^ 2 = (sin β ^ 2 + sin γ ^ 2 - 2 * sin β * sin γ * cos α) / sin α ^ 2 := by
      have eq4 : sin α ^ 2 + sin β ^ 2 - 2 * sin α * sin β * cos γ = sin γ ^ 2 := by 
        have h10 : γ = π - (α + β) := by 
          linarith 
        have h11 : sin γ = sin (α + β) := by 
          have h12 : γ = π - (α + β) := by 
            linarith 
          rw [h12]
          have h13 : sin (π - (α + β)) = sin (α + β) := by
            rw [sin_pi_sub]
          linarith 
        have h12 : cos γ = - cos (α + β) := by 
          have h13 : γ = π - (α + β) := by 
            linarith 
          rw [h13]
          have h14 : cos (π - (α + β)) = - cos (α + β) := by 
            rw [cos_pi_sub]
          linarith 
        have h13 : cos (α + β) = cos α * cos β - sin α * sin β := by 
          rw [cos_add]
        rw [h11, h12, h13]
        have h14 : sin (α + β) = sin α * cos β + cos α * sin β := by 
          rw [sin_add]
        rw [h14]
        <;> nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h1 h2, mul_pos h1 (show (0 : Real) < sin γ by linarith), mul_pos h2 (show (0 : Real) < sin γ by linarith)]
      rw [eq4, eq1]
      <;> field_simp [show sin γ ^ 2 > 0 by nlinarith [h3], show sin α ^ 2 > 0 by nlinarith [h1]]
      <;> nlinarith 
    exact eq3