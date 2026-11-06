import Mathlib 

/-Let $C$ be the circle with equation $x^2-6y-3=-y^2-4x$. If $(a,b)$ is the center of $C$ and $r$ is its radius, what is the value of $a+b+r$?-/
theorem algebra_10218 {a b r : ℝ} (hr : 0 < r) (h : ∀ x y : ℝ, x ^ 2 - 6 * y - 3 = - y ^ 2 - 4 * x ↔ (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) :
    a + b + r = 5 := by
  -- simplify x ^ 2 - 6 * y - 3 = -y ^ 2 - 4 * x to (x + 2) ^ 2 + (y - 3) ^ 2 = 16
  have eq : ∀ x y : ℝ, x ^ 2 - 6 * y - 3 = - y ^ 2 - 4 * x ↔ (x + 2) ^ 2 + (y - 3) ^ 2 = 16 := by
    intro x y
    apply Iff.intro <;> intro h₁
    ring_nf at h₁ ⊢
    linarith only [h₁]
    ring_nf at h₁ ⊢
    linarith only [h₁]
  -- so we have (x + 2) ^ 2 + (y - 3) ^ 2 = 16 ↔ (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2
  have eq₀ : ∀ x y : ℝ, (x + 2) ^ 2 + (y - 3) ^ 2 = 16 ↔ (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2 := by
    intro x y
    rw [<-eq x y]
    exact h x y
  clear eq h
  -- show that b = 3
  have hb : b = 3 := by
    have eq₁ := eq₀ (-2) (-1)
    have eq₂ := eq₀ (-2) 7
    norm_num at eq₁ eq₂
    have eq : (-1 - b) ^ 2 - (7 - b) ^ 2 = 0 := by linarith only [eq₁, eq₂]
    ring_nf at eq
    linarith only [eq]
  -- show that a = -2
  have ha : a = -2 := by
    have eq₁ := eq₀ 2 3
    have eq₂ := eq₀ (-6) 3
    norm_num at eq₁ eq₂
    have eq : (2 - a) ^ 2 - (-6 - a) ^ 2 = 0 := by linarith only [eq₁, eq₂]
    ring_nf at eq
    linarith only [eq]
  -- show that r ^ 2 = 16
  have hr₂ : r ^ 2 = 16 := by
    have eq₁ := eq₀ 2 3
    norm_num at eq₁
    rw [ha, hb] at eq₁
    norm_num at eq₁
    linarith only [eq₁]
  -- so we have r = 4 by r > 0
  replace hr : r = 4 := by nlinarith only [hr, hr₂]
  clear hr₂
  -- substitute the a, b, r in the conclusion
  rw [ha, hb, hr]
  norm_num