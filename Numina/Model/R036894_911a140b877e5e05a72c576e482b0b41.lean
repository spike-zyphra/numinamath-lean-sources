import Mathlib

theorem inequalities_602299 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (h₀ : ∀ i, |a i| ≤ 2) (h₁ : ∑ i, (a i)^3 = 0) :
    ∑ i, a i ≤ 2 / 3 * n := by
  have h2 : ∀ i, -2 ≤ a i ∧ a i ≤ 2 := by
    intro i
    have h := h₀ i
    cases abs_le.mp h with
    | intro h₁ h₂ => exact ⟨by linarith, by linarith⟩
  have h3 : ∀ i, (a i) ^ 3 ≥ 3 * (a i) - 2 := by
    intro i
    have h4 : -2 ≤ a i ∧ a i ≤ 2 := h2 i
    nlinarith [sq_nonneg ((a i) - 1), sq_nonneg ((a i) + 2), h4.1, h4.2]
  have h4 : ∑ i, (a i)^3 ≥ ∑ i, (3 * (a i) - 2) := by
    apply Finset.sum_le_sum
    intro i _
    have h_i : (a i) ^ 3 ≥ 3 * (a i) - 2 := h3 i
    linarith
  have h5 : ∑ i, (3 * (a i) - 2) = 3 * (∑ i, a i) - 2 * (n : ℝ) := by
    calc
      ∑ i, (3 * (a i) - 2)
        = 3 * (∑ i, (a i)) - ∑ i, (2 : ℝ) := by
          rw [Finset.sum_sub_distrib]
          congr
          · rw [Finset.mul_sum]
          all_goals
            simp
      _ = 3 * (∑ i, (a i)) - (∑ i, (2 : ℝ)) := by ring
      _ = 3 * (∑ i, (a i)) - (2 * (↑n : ℝ)) := by
        simp
        <;> ring_nf <;> simp
      _ = 3 * (∑ i, a i) - 2 * (↑n : ℝ) := by
        norm_num
    <;> simp
    <;> ring_nf
    <;> simp
    <;> norm_num
  linarith [h₁, h4, h5]