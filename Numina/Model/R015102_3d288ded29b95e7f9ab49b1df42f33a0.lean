import Mathlib

theorem other_87830 (α : ℝ) (hα : α > 0) (a : ℕ → ℝ)
    (ha0 : a 0 = α) (han : ∀ n, a (n + 1) = a n / (1 + a n)) :
    ∀ n, a n = α / (1 + α * n) := by 
  intro n 
  induction n with 
  | zero => 
    rw [ha0]
    field_simp 
  | succ n ih => 
    have eq1 : a (n + 1) = a n / (1 + a n) := han n 
    rw [eq1] 
    rw [ih] 
    field_simp at *
    <;> ring_nf <;> field_simp at *