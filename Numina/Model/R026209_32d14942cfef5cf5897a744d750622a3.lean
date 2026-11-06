import Mathlib


open Real


theorem algebra_134078 {f : ℝ → ℝ} (h0 : f 0 = 1 / 2) (ha : ∃ a, ∀ x y, f (x + y) = f x * f (a - y) + f y * f (a - x)) :
    ∃ c, ∀ x, f x = c := by
  rcases ha with ⟨a, hax⟩
  have h1 : f (0 + (0 : ℝ)) = f (0) * f (a - (0 : ℝ)) + f (0) * f (a - (0 : ℝ)) := hax 0 0
  have eq1 : f (0) = 2 * f (0) * f (a) := by
    simp at h1 ⊢
    nlinarith
  have ha1 : f (a) = 1 / 2 := by
    rw [h0] at eq1
    nlinarith
  -- Now, we prove that for all $x$, $f x = f(a - x)$.
  have eq2 : ∀ x : ℝ, f x = f (a - x) := by
    intro x
    have h2 : f (x + (0 : ℝ)) = f x * f (a - (0 : ℝ)) + f (0) * f (a - x) := hax x 0
    simp at h2 ⊢
    rw [ha1] at h2
    rw [h0] at h2
    linarith
  -- Let's prove that $f(2x) = 2(f x)^2$ for all $x$.
  have eq3 : ∀ x : ℝ, f (2 * x) = 2 * (f x) ^ 2 := by
    intro x
    have h4 : f (x + x) = f x * f (a - x) + f x * f (a - x) := hax x x
    have h5 : f (a - x) = f x := by
      have hx1 : f x = f (a - x) := eq2 x
      linarith
    have h6 : f (x + x) = 2 * (f x) ^ 2 := by
      rw [h5] at h4
      nlinarith
    rw [show x + x = (2 * x : ℝ) by ring] at h6
    linarith
  -- Let's prove that $(f x)^2 = \frac{1}{4}$ for all $x$.
  have eq4 : ∀ x : ℝ, (f x) ^ 2 = 1 / 4 := by
    intro x
    have h7 : f ((a - x) + x) = f (a - x) * f (a - x) + f x * f (a - (a - x)) := hax (a - x) x
    have h8 : (a - x : ℝ) + (x : ℝ) = (a : ℝ) := by ring
    rw [h8] at h7
    have h9 : f (a - x) = f x := by
      have hx1 : f x = f (a - x) := eq2 x
      linarith
    have h10 : a - (a - x : ℝ) = (x : ℝ) := by ring
    rw [ha1] at h7
    rw [h9] at h7
    rw [h10] at h7
    nlinarith
  -- Let's prove that $f(2x) = 1/2$ for all $x$.
  have eq5 : ∀ x : ℝ, f (2 * x) = 1 / 2 := by
    intro x
    have h11 : f (2 * x) = 2 * (f x) ^ 2 := eq3 x
    have h12 : (f x) ^ 2 = 1 / 4 := eq4 x
    rw [h12] at h11
    linarith
  -- Now we can prove that f is constant.
  use (1 / 2)
  intro x
  have h13 : f (2 * (x / 2)) = 1 / 2 := eq5 (x / 2)
  have h14 : 2 * (x / 2) = x := by
    ring
  rw [h14] at h13
  linarith