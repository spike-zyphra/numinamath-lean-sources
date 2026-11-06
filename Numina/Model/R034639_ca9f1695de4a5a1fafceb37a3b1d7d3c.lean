import Mathlib

theorem algebra_195041 {f g : ℝ→ℝ}
    (hf : ∀x, f x = (x / 4) * 0.96)
    (hg : ∀x, g x = (x * 4) * 1.04) :
    (∀x ≠ 0, round ((x / g (f x) - 1) * 10000) = 16) := by
  intro x hx
  have eq1 : g (f x) = x * (0.96 * 1.04) := by
    rw [hf x]
    rw [hg]
    ring_nf
  -- We compute x / g (f x) - 1
  -- x / g(f x) = x / (x * 0.96 * 1.04) = 1 / (0.96 * 1.04)
  have eq2 : x / g (f x) - 1 = (1 / (0.96 * 1.04) - 1) := by
    rw [eq1]
    have hx0 : x ≠ 0 := hx
    field_simp [hx0]
    <;> ring
  -- We compute the product by 10000
  have h3 : (x / g (f x) - 1) * 10000 = ( (1 / (0.96 * 1.04) - 1 ) * 10000 ) := by 
    rw [eq2]
    all_goals ring
  rw [h3]
  norm_num [round_eq]
  all_goals norm_num