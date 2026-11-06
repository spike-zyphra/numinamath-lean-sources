import Mathlib

theorem algebra_120466 {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (-5) 3, f (x + 1) ≠ 0)
    (h : ∀ x, f x + f (-x) = 0) (h' : f (-1) = 0) (h'' : MonotoneOn f (Set.Ico (-4) 0))
    (h''' : ¬∃ B, ∀ x, f x ≤ B) :
    {x | x^3 * f x ≤ 0} = {x | -4 ≤ x ∧ x ≤ -1} := by
  have h1 : (-2 : ℝ) ∈ Set.Icc (-5 : ℝ) 3 := by
    norm_num
  have h2 := hf (-2) h1
  have h3 : f (-2 + 1) = f (-1) := by ring_nf
  have h4 : f (-1) ≠ 0 := by
    have h4 : f (-2 + 1) ≠ 0 := h2
    rw [h3] at h4
    exact h4
  contradiction