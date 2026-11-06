import Mathlib

theorem algebra_111125 {a b x1 x2 : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hxy : x1 ≠ x2) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x)
    (h : f x1 = f x2) : f (x1 + x2) = 0 := by
  have eq1 : f x1 = a * x1 ^ 2 + b * x1 := hf x1
  have eq2 : f x2 = a * x2 ^ 2 + b * x2 := hf x2
  have eq3 : f (x1 + x2) = a * (x1 + x2) ^ 2 + b * (x1 + x2) := hf (x1 + x2)
  rw [eq1, eq2] at h
  have eq4 : a * x1 ^ 2 + b * x1 - (a * x2 ^ 2 + b * x2) = 0 := by linarith
  have eq5 : (x1 - x2) * (a * (x1 + x2) + b) = 0 := by
    ring_nf at eq4 ⊢ 
    linarith
  have eq6 : a * (x1 + x2) + b = 0 := by
    apply_fun (λ y => y / (x1 - x2)) at eq5
    field_simp [(show x1 - x2 ≠ 0 by intro h1; apply hxy; linarith)] at eq5
    linarith
  rw [eq3]
  have eq7 : a * (x1 + x2) ^ 2 + b * (x1 + x2) = (x1 + x2) * (a * (x1 + x2) + b) := by ring
  rw [eq7]
  rw [eq6]
  norm_num