import Mathlib

open Real

theorem inequalities_72361 (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i ≤ 1) :
    ∑ i, x i / (1 + (n - 1) * x i) ≤ 1 := by
  have h1 : ∀ i, 0 < x i ∧ x i ≤ 1 := hx
  have h2 : ∀ i, x i / (1 + (n - 1) * x i) ≤ 1 / (n : ℝ) := by
    intro i
    rcases h1 i with ⟨hx1, hx2⟩
    have hx3 : (0 : ℝ) < x i := hx1
    have hx4 : x i ≤ (1 : ℝ) := hx2
    have h3 : (0 : ℝ) < 1 + (n - 1 : ℝ) * x i := by
      have h4 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
      have h5 : (n - 1 : ℝ) ≥ (0 : ℝ) := by
        have h6 : (n : ℝ) ≥ (1 : ℝ) := h4
        nlinarith
      nlinarith [h5, hx1]
    have h4 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
    have h9 : x i / (1 + (n - 1 : ℝ) * x i) ≤ 1 / (n : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h11 : (n : ℝ) * x i - (n - 1 : ℝ) * x i ≤ (1 : ℝ) := by
        have h12 : (n : ℝ) - (n - 1 : ℝ) = (1 : ℝ) := by
          ring_nf
        have h13 : (n : ℝ) * x i - (n - 1 : ℝ) * x i = ((n : ℝ) - (n - 1 : ℝ)) * x i := by
          ring_nf
        rw [h13, h12]
        nlinarith
      have h7 : (n : ℝ) * x i ≤ (1 + (n - 1 : ℝ) * x i) := by linarith
      linarith
    linarith
  have h10 : ∑ i, x i / (1 + (n - 1) * x i) ≤ ∑ i : Fin n, (1 / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h2 i
    simpa using h2
  have h11 : ∑ i : Fin n, (1 / (n : ℝ)) = 1 := by
    have h4 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ n by linarith)
    simp
    <;> field_simp
    <;> ring_nf
  linarith [h10, h11]