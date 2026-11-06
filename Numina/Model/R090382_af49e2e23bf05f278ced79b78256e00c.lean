import Mathlib

theorem algebra_324206 (f g : ℝ → ℝ) (m : ℝ)
    (hf : f = fun x => x ^ 2) (hg : g = fun x => 2 * x + 2 * m)
    (hF : ∀ x, f (g x) - g (f x) ≥ 1 / 4) :
    m = -1 / 4 := by
  have h_eq1 : ∀ x, f (g x) - g (f x) = 2 * x ^ 2 + 8 * m * x + 4 * m ^ 2 - 2 * m := by
    intro x
    rw [hf, hg]
    simp
    ring_nf
  have h1 := hF (-2 * m)
  have h_eq2 : f (g (-2 * m)) - g (f (-2 * m)) = -4 * m ^ 2 - 2 * m := by
    rw [h_eq1]
    ring_nf
  have h2 : -4 * m ^ 2 - 2 * m ≥ 1 / 4 := by
    linarith [h1, h_eq2]
  have h4 : f (g (0 : ℝ)) - g (f (0 : ℝ)) ≥ 1 / 4 := hF 0
  have h_eq3 : f (g (0 : ℝ)) - g (f (0 : ℝ)) = 4 * m ^ 2 - 2 * m := by
    rw [h_eq1]
    norm_num
  have h3 : 4 * m ^ 2 - 2 * m ≥ 1 / 4 := by
    linarith [h4, h_eq3]
  have h4 : (4 * m + 1) ^ 2 = 0 := by
    nlinarith [h2, h3]
  have h5 : 4 * m + 1 = 0 := by
    rw [sq_eq_zero_iff] at h4
    exact h4
  have h6 : m = -1 / 4 := by
    linarith [h5]
  exact h6