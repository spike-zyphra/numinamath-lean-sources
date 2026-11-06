import Mathlib

theorem number_theory_6088 (n : ℕ) :
    Set.Infinite {(x, y, z) : ℝ × ℝ × ℝ | x^n + y^n = z^(n + 1)} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (k : ℕ) => ((2 : ℝ) * (k : ℝ) ^ (n + 1), (2 : ℝ) * (k : ℝ) ^ (n + 1), (2 : ℝ) * (k : ℝ) ^ n))
  · -- Show that the function f is injective
    intro k1 k2 h
    simp [Prod.ext_iff] at h ⊢
    linarith
  · -- Show that for all k, f(k) is in the set
    intro k
    simp [Prod.ext_iff]
    <;> ring_nf <;> simp <;> ring