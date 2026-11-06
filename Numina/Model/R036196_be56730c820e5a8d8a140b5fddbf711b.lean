import Mathlib

theorem algebra_16343 (m M : ℝ) (S : Set ℝ) (hS : S = { (x) | (x : ℝ) (y : ℝ) (z : ℝ) (_ : x + y + z = 4) (_ : x^2 + y^2 + z^2 = 6)}) (hm : IsLeast S m) (hM : IsGreatest S M) :
  m + M = 8 / 3 := by
  have h1 : m ∈ S := hm.left
  have h2 : ∀ x ∈ S, m ≤ x := hm.right
  have h3 : M ∈ S := hM.left
  have h4 : ∀ x ∈ S, x ≤ M := hM.right

  have h5 : (2 : ℝ) ∈ S := by
    rw [hS]
    use 2, 1, 1
    norm_num

  have h6 : (2 / 3 : ℝ) ∈ S := by
    rw [hS]
    use 2 / 3, 5 / 3, 5 / 3
    constructor
    · -- Show x+y+z = 4
      norm_num
    · -- Show x^2+y^2+z^2 = 6
      norm_num

  have h8 : m ≥ (2 / 3 : ℝ) := by
    have h9 : m ∈ S := h1
    rw [hS] at h9
    rcases h9 with ⟨x, y, z, h_eq1, h_eq2, h11⟩
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 2 * x), sq_nonneg (x - 2 / 3), sq_nonneg (x - 2)]

  have h10 : m ≤ (2 / 3 : ℝ) := by
    have h11 : (2 / 3 : ℝ) ∈ S := h6
    have h12 : m ≤ (2 / 3 : ℝ) := by
      apply h2
      exact h11
    linarith

  have hm2 : m = (2 / 3 : ℝ) := by
    linarith

  have h9 : M ≤ (2 : ℝ) := by
    have h10 : M ∈ S := h3
    rw [hS] at h10
    rcases h10 with ⟨x, y, z, h_eq1, h_eq2, h11⟩
    nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 2 * x), sq_nonneg (x - 2 / 3), sq_nonneg (x - 2)]

  have h12 : (2 : ℝ) ≤ M := by
    have h11 : (2 : ℝ) ∈ S := h5
    have h13 : (2 : ℝ) ≤ M := by
      apply h4
      exact h11
    linarith

  have hM2 : M = (2 : ℝ) := by
    linarith

  rw [hm2, hM2]
  norm_num