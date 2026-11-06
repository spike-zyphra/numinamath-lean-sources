import Mathlib

open Real

theorem algebra_298372 {a : ℝ} (ha : a ≠ 0 ∧ a ≠ 1)
    (hsum : ∀ n, ∑ i in Finset.range n, a ^ i = a / (1 - a) * (1 - a ^ n))
    (b : ℕ → ℝ) (hb : ∀ n, b n = a ^ n * log (|a ^ n|)) :
    ∃ m, ∀ n, 0 < n → b n ≥ b m ↔ m = 8 := by 
  have h0 := hsum 0
  have h1 := hsum 1
  norm_num [Finset.sum_range_succ] at h0 h1
  have h2 : a = 1 := by 
    have eq1 : a / (1 - a) * (1 - a) = a := by 
      have hne : (1 - a) ≠ 0 := by 
        intro h'
        apply ha.2 
        linarith 
      field_simp [hne]
    rw [eq1] at h1 
    linarith
  have h3 : a ≠ 1 := ha.2
  exfalso 
  exact h3 h2