import Mathlib

theorem algebra_9424 {a b : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + a * x + b)
    (hzeros : f (-2) = 0 ∧ f 3 = 0) :
    {x | a * f (- 2 * x) > 0} = {x | -3 / 2 < x ∧ x < 1} := by

  have h1 : (-2) ^ 2 + a * (-2) + b = 0 := by 
    rw [hf] at hzeros
    exact hzeros.1

  have h2 : (3 : ℝ) ^ 2 + a * 3 + b = 0 := by 
    rw [hf] at hzeros
    exact hzeros.2

  have ha : a = -1 := by 
    nlinarith

  have hb : b = -6 := by
    nlinarith [h1, h2, ha]

  ext x
  simp [hf, ha, hb]
  constructor
  · -- Assume a * f (-2 * x) > 0. prove -3 / 2 < x ∧ x < 1
    intro h
    constructor
    · -- Show -3/2 < x
      nlinarith 
    · -- Show x < 1
      nlinarith 
  · -- Assume -3/2 < x ∧ x < 1, prove a * f (-2 * x) > 0
    rintro ⟨h1, h2⟩ 
    nlinarith