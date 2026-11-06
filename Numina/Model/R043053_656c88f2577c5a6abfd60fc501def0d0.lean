import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_291117 :
  let weight₁ := 1200; 
  let weight₂ := 1600; 
  let power := 15 * 75; 
  let ρ := 1/20;       
  let e := 1/30;       
  
  {(v₁, v₂, v₃, v₄) : ℝ × ℝ × ℝ × ℝ | 
    ρ * weight₁ * v₁ = power ∧                       
    (ρ + e) * weight₁ * v₂ = power ∧                 
    ρ * weight₂ * v₃ = power ∧                       
    (ρ + e) * weight₂ * v₄ = power                   
  } =
  {(18.75, 11.25, 14.0625, 8.4375)}
  := by
  ext ⟨v₁, v₂, v₃, v₄⟩
  simp [-one_div]
  constructor
  · -- Assume (v₁, v₂, v₃, v₄) satisfies the system
    rintro ⟨eq₁, eq₂, eq₃, eq₄⟩
    have h₁ : v₁ = 18.75 := by
      linarith
    have h₂ : v₂ = 11.25 := by
      linarith
    have h₃ : v₃ = 14.0625 := by
      linarith
    have h₄ : v₄ = 8.4375 := by
      linarith
    simp [h₁, h₂, h₃, h₄]
  · -- Assume (v₁, v₂, v₃, v₄) is the given solution
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · -- First equation
      norm_num
    constructor
    · -- Second equation
      norm_num
    constructor
    · -- Third equation
      norm_num
    · -- Fourth equation
      norm_num