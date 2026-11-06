import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11056 {f : ℝ → ℝ} (hf : f = λ x => 16 * x + 3)
  (hinv : Function.LeftInverse (f⁻¹) f) :
  ∑ᶠ x ∈ {x | f⁻¹ x = f ((2 * x)⁻¹)}, x = 51 := by

  have h1 : ∀ x, f x = 16 * x + 3 := by simp [hf]

  have h2 : ∀ y, f⁻¹ y = (y - 3) / 16 := by
    intro y
    have h3 : ∀ x, f x = y ↔ x = (y - 3) / 16 := by
      intro x
      constructor
      · intro hfx
        rw [h1] at hfx
        linarith
      · intro hx
        rw [h1, hx]
        linarith
    have h4 : f⁻¹ y = (y - 3) / 16 := by
      have h5 : f ((y - 3) / 16) = y := by 
        rw [h1]
        ring
      calc 
        f⁻¹ y = f⁻¹ (f ((y - 3) / 16)) := by rw [h5]
        _ = (y - 3) / 16 := by apply hinv
    exact h4

  have eqn : ∀ x, f⁻¹ x = f ((2 * x)⁻¹) ↔ x^2 - 51 * x - 128 = 0 := by
    intro x
    constructor
    · -- Assume f⁻¹ x = f ((2 * x)⁻¹), then x^2 -51x -128 =0
      intro heq
      rw [h2 x] at heq
      have h2x : (2 * x)⁻¹ = 1 / (2 * x) := by field_simp
      rw [h2x] at heq
      rw [h1] at heq 
      have h3 : x ≠ 0 := by
        by_contra h
        rw [h] at heq
        norm_num [h2 x] at heq
      field_simp [h3] at heq
      ring_nf at heq ⊢
      linarith

    · -- Assume x^2 -51x -128 =0, then f⁻¹ x = f ((2 * x)⁻¹)
      intro heq
      have h2x : f⁻¹ x = (x - 3) / 16 := h2 x
      rw [h2x]
      have h3x : (2 * x)⁻¹ = 1 / (2 * x) := by field_simp
      rw [h3x]
      rw [h1]
      have h3 : x ≠ 0 := by
        by_contra h
        rw [h] at heq
        nlinarith
      field_simp [h3] at *
      nlinarith [heq]

  have h3 : {x | f⁻¹ x = f ((2 * x)⁻¹)} = { (51 + Real.sqrt 3113) / 2, (51 - Real.sqrt 3113) / 2 } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume f⁻¹ x = f ((2 * x)⁻¹)
      intro h
      have heq : x^2 - 51 * x - 128 = 0 := eqn x |>.1 h
      have h4 : (x - (51 + Real.sqrt 3113) / 2) * (x - (51 - Real.sqrt 3113) / 2) = 0 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (3113 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h4) with h5 h6
      · -- Case where x = (51 + √3113)/2
        left
        linarith
      · -- Case where x = (51 - √3113)/2
        right
        linarith

    · -- Assume x ∈ { (51 ±√3113)/2 }, then prove f⁻¹ x = f ((2 * x)⁻¹)
      rintro (h | h)
      · -- Case where x = (51 + Real.sqrt 3113)/2
        have heq : x^2 - 51 * x - 128 = 0 := by
          rw [h]
          nlinarith [Real.sq_sqrt (show 0 ≤ (3113 : ℝ) by norm_num)]
        have h_eq1 : f⁻¹ x = f ((2 * x)⁻¹) := (eqn x).2 heq
        exact h_eq1
      · -- Case where x = (51 - Real.sqrt 3113)/2
        have heq : x^2 - 51 * x - 128 = 0 := by
          rw [h]
          nlinarith [Real.sq_sqrt (show 0 ≤ (3113 : ℝ) by norm_num)]
        have h_eq1 : f⁻¹ x = f ((2 * x)⁻¹) := (eqn x).2 heq
        exact h_eq1

  rw [h3]
  rw [finsum_mem_pair]
  · -- Show sum is 51
    field_simp
    <;> ring
  · -- Show the two elements are distinct
    intro h
    have h1 : Real.sqrt 3113 = 0 := by linarith
    have h2 : 0 < (3113 : ℝ) := by norm_num
    have h3 : 0 < Real.sqrt 3113 := Real.sqrt_pos.2 (by linarith : (3113 : ℝ) > 0)
    linarith [h1, h3]