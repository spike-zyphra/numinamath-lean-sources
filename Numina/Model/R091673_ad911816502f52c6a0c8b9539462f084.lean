import Mathlib

theorem algebra_245987 {n : ℕ} (hn : n ≥ 2) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.Icc 1 n, a i > 1) (h : ∀ k ∈ Finset.Icc 1 (n - 1), |a (k + 1) - a k| < 1) :
    ∃ k ∈ Finset.Icc 1 n, |a k - a 1| < 1 := by
  use 1
  constructor
  · -- Show that 1 ∈ Finset.Icc 1 n
    exact Finset.mem_Icc.mpr ⟨by norm_num, by linarith⟩
  · -- Show that |a 1 - a 1| < 1
    simp
    <;> try { linarith }