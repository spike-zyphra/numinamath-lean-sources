import Mathlib

open Real Set
open scoped Real

theorem inequalities_107551 (α β γ : Real) (h : α ∈ Ioo 0 (π / 2)) (h' : β ∈ Ioo 0 (π / 2))
    (h'' : γ ∈ Ioo 0 (π / 2)) (h''' : α + β + γ = π) :
    sin (2 * α) + sin (2 * β) + sin (2 * γ) ≤ sin (α + β) + sin (β + γ) + sin (γ + α) := by

  rcases h with ⟨hα1, hα2⟩
  rcases h' with ⟨hβ1, hβ2⟩
  rcases h'' with ⟨hγ1, hγ2⟩

  have h1 : sin (α + β) = sin γ := by 
    have h2 : α + β = π - γ := by linarith [h''']
    rw [h2]
    have h3 : sin (π - γ) = sin γ := by 
      rw [sin_pi_sub]
    exact h3

  have h2 : sin (β + γ) = sin α := by 
    have h4 : β + γ = π - α := by linarith [h''']
    rw [h4]
    have h5 : sin (π - α) = sin α := by 
      rw [sin_pi_sub]
    exact h5

  have h3 : sin (γ + α) = sin β := by 
    have h6 : γ + α = π - β := by linarith [h''']
    rw [h6]
    have h7 : sin (π - β) = sin β := by 
      rw [sin_pi_sub]
    exact h7

  have h4 : sin (α + β) + sin (β + γ) + sin (γ + α) = sin α + sin β + sin γ := by
    rw [h1, h2, h3]
    all_goals try { ring }

  have h5 : sin (2 * α) + sin (2 * β) + sin (2 * γ) = 2 * sin α * cos α + 2 * sin β * cos β + 2 * sin γ * cos γ := by
    have h6 : sin (2 * α) = 2 * sin α * cos α := by
      rw [show 2 * α = 2 * α by rfl]
      rw [sin_two_mul]
    have h7 : sin (2 * β) = 2 * sin β * cos β := by
      rw [show 2 * β = 2 * β by rfl]
      rw [sin_two_mul]
    have h8 : sin (2 * γ) = 2 * sin γ * cos γ := by
      rw [show 2 * γ = 2 * γ by rfl]
      rw [sin_two_mul]
    linarith [h6, h7, h8]

  rw [h4, h5]

  have h6 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have h7 : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]

  have h8 : cos γ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hγ1, hγ2, Real.pi_pos]
    linarith [hγ1, hγ2, Real.pi_pos]

  have h9 : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have h10 : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hβ1, hβ2, Real.pi_pos]
    linarith [hβ1, hβ2, Real.pi_pos]

  have h11 : sin γ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hγ1, hγ2, Real.pi_pos]
    linarith [hγ1, hγ2, Real.pi_pos]

  have h13 : sin α + sin β + sin γ - 2 * (sin α * cos α + sin β * cos β + sin γ * cos γ) ≥ 0 := by
    have h13 : sin γ = sin α * cos β + cos α * sin β := by
      have h14 : γ = π - (α + β) := by linarith [h''']
      rw [h14]
      have h15 : sin (π - (α + β)) = sin (α + β) := by
        rw [sin_pi_sub]
      rw [h15]
      have h16 : sin (α + β) = sin α * cos β + cos α * sin β := by
        rw [sin_add]
        <;> ring
      rw [h16]
    have h14 : sin α = sin β * cos γ + cos β * sin γ := by
      have h15 : α = π - (β + γ) := by linarith [h''']
      rw [h15]
      have h16 : sin (π - (β + γ)) = sin (β + γ) := by
        rw [sin_pi_sub]
      rw [h16]
      have h17 : sin (β + γ) = sin β * cos γ + cos β * sin γ := by
        rw [sin_add]
        <;> ring
      rw [h17]
    have h15 : sin β = sin γ * cos α + cos γ * sin α := by
      have h16 : β = π - (γ + α) := by linarith [h''']
      rw [h16]
      have h17 : sin (π - (γ + α)) = sin (γ + α) := by
        rw [sin_pi_sub]
      rw [h17]
      have h18 : sin (γ + α) = sin γ * cos α + cos γ * sin α := by
        rw [sin_add]
        <;> ring
      rw [h18]

    nlinarith [sq_nonneg (sin α - sin β), sq_nonneg (sin β - sin γ), sq_nonneg (sin γ - sin α),
        sq_nonneg (cos α - cos β), sq_nonneg (cos β - cos γ), sq_nonneg (cos γ - cos α),
        Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq γ,
        mul_pos h9 h10, mul_pos h9 h11, mul_pos h10 h11,
        mul_pos h6 h7, mul_pos h6 h8, mul_pos h7 h8
      ]
  linarith