import Mathlib

theorem algebra_80836 {b c : ℝ} (hb : b ≠ 1) (hc : c ≠ 1)
    (h1 : ∃ d, 1 + d = b ∧ b + d = c) (h2 : ∃ r, 1 * r = c ∧ c * r = b) :
    100 * (b - c) = 75 := by
  rcases h1 with ⟨d, had⟩
  rcases h2 with ⟨r, hgr⟩

  have ad₁ := had.1
  have ad₂ := had.2

  have eq1 : c = 2 * b - 1 := by
    linarith [ad₁, ad₂]

  have g₁ := hgr.1
  have g₂ := hgr.2

  have eq3 : c = r := by
    linarith

  have eq4 : r^2 = b := by
    rw [eq3] at g₂
    nlinarith

  have eq5 : 2 * r^2 - r - 1 = 0 := by
    rw [eq3] at eq1
    nlinarith [eq1, eq4]

  have individual_solutions : (r - 1) * (2 * r + 1) = 0 := by
    nlinarith [eq5]

  cases' (mul_eq_zero.mp individual_solutions) with h10 h20

  · -- Case $r = 1$ is impossible because $b \neq 1$.
    have hr₁ : r = 1 := by linarith
    have hb₁ : b = 1 := by
      nlinarith [eq4, hr₁]
    exfalso
    exact hb (hb₁)

  · -- Case $r = -1/2$ gives us the solution.
    have hr₂ : r = -1/2 := by linarith
    have hb₂ : b = 1/4 := by
      nlinarith [eq4, hr₂]
    have hc₂ : c = -1/2 := by
      rw [eq3]
      linarith [hr₂]
    nlinarith [hb₂, hc₂]