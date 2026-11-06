import Mathlib

open Real

theorem algebra_13922 {f : ℝ → ℝ} (hf : f = fun x => 2 * x + 1) :
    ∑ᶠ x ∈ {x | f ⁻¹' {x} = {f (x⁻¹)}}, x = 3 := by
  have h1 : ∀ x, f x = 2 * x + 1 := by
    intro x; rw [hf]
  
  have h2 : ∀ x : ℝ, f ⁻¹' {x} = { (x - 1) / 2 } := by
    intro x
    ext y
    simp [h1]
    constructor
    · -- Assume h : f y = x
      intro h
      linarith
    · -- Assume h : (x - 1) / 2 = y
      intro h
      linarith
  have h3 : ∀ x : ℝ, f (x⁻¹) = 2 * (1 / x) + 1 := by
    intro x
    rw [h1]
    all_goals simp
    <;> ring

  have h4 : {x : ℝ | f ⁻¹' {x} = {f (x⁻¹)}} = {4, -1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, h2, h3]
    constructor
    · -- First direction
      intro h
      have eq1 : x ≠ 0 := by
        by_contra h11
        rw [h11] at h
        norm_num [h11] at h
        <;> tauto
      have h5 : (x - 1) / 2 = 2 * (1 / x) + 1 := by
        have h6 : ( (x - 1 ) / 2 ) = ( 2 * (1 / x) + 1 ) := by
          have hne : x ≠ 0 := eq1
          field_simp [hne] at h ⊢
          <;> linarith
        linarith
      have eq4 : x ^ 2 - 3 * x - 4 = 0 := by
        field_simp [eq1] at h5
        nlinarith [h5]
      have eq5 : x = 4 ∨ x = -1 := by
        have h2 : x ^ 2 - 3 * x - 4 = 0 := eq4
        have h34 : (x - 4) * (x + 1) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h34 ) with h44 h11
        · -- Case h44: x - 4 = 0
          left
          linarith
        · -- Case h11: x + 1 = 0
          right
          linarith
      tauto
    · -- Second direction
      rintro (h | h)
      · -- x = 4
        rw [show x = 4 by linarith]
        norm_num [h1]
      · -- x = -1
        rw [show x = -1 by linarith]
        norm_num [h1]
  rw [h4]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num