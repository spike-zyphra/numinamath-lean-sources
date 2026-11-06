import Mathlib

theorem algebra_192975 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (b c : ℝ)
    (hsum1 : ∑ i, (i + 1) * a i = b) (hsum2 : ∑ i, (i + 1)^2 * a i = c)
    (h : c = b^2) : ∃ m : ℤ, b = m := by

  have h1 : ∑ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = 0 := by
    have eq2 : ∑ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = c - b ^ 2 := by
      have h3 : ∑ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = ∑ i : Fin n, ((i.1 + 1 : ℝ) ^ 2 * a i) - 2 * b * (∑ i : Fin n, ((i.1 + 1 : ℝ) * a i)) + b ^ 2 * (∑ i : Fin n, (a i : ℝ)) := by
        have h4 : ∀ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = (i.1 + 1 : ℝ) ^ 2 * a i - 2 * b * ((i.1 + 1 : ℝ) * a i) + b ^ 2 * (a i : ℝ) := by
          intro i
          ring
        calc 
          ∑ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = ∑ i : Fin n, (((i.1 + 1 : ℝ) ^ 2 * a i) - 2 * b * ((i.1 + 1 : ℝ) * a i) + b ^ 2 * (a i : ℝ)) := by
            apply Finset.sum_congr rfl; intro i _
            specialize h4 i
            linarith
          _ = ∑ i : Fin n, ((i.1 + 1 : ℝ) ^ 2 * a i) - 2 * b * (∑ i : Fin n, ((i.1 + 1 : ℝ) * a i)) + b ^ 2 * (∑ i : Fin n, (a i : ℝ)) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, sub_eq_add_neg]
      rw [h3, hsum2, hsum1, hsum]
      all_goals
        ring
    rw [eq2, h]
    all_goals
      norm_num

  have h2 : ∀ i : Fin n, ((i.1 + 1 : ℝ) - b) ^ 2 * a i = 0 := by
    intro i
    have eq3 : 0 ≤ ((i.1 + 1 : ℝ) - b) ^ 2 * a i := by
      have eq4 : 0 ≤ ((i.1 + 1 : ℝ) - b) ^ 2 := by
        apply sq_nonneg
      have eq5 : 0 ≤ a i := ha i
      nlinarith
    have eq6 : ∑ j : Fin n, ((j.1 + 1 : ℝ) - b) ^ 2 * a j = 0 := h1
    have eq7 : ((i.1 + 1 : ℝ) - b) ^ 2 * a i ≤ ∑ j : Fin n, ((j.1 + 1 : ℝ) - b) ^ 2 * a j := by
      apply Finset.single_le_sum (fun j _ => by 
        have eq3' : 0 ≤ ((j.1 + 1 : ℝ) - b) ^ 2 * a j := by
          have eq4' : 0 ≤ ((j.1 + 1 : ℝ) - b) ^ 2 := by
            apply sq_nonneg
          have eq5' : 0 ≤ a j := ha j
          nlinarith
        exact eq3'
      ) (show i ∈ Finset.univ by simp)
    have eq8 : ((i.1 + 1 : ℝ) - b) ^ 2 * a i ≤ (0 : ℝ) := by linarith [eq7, eq6]
    have eq9 : ((i.1 + 1 : ℝ) - b) ^ 2 * a i ≥ 0 := eq3
    linarith

  by_cases h10 : (∀ i : Fin n, a i = 0)
  · 
    have h3 : ∑ i : Fin n, a i = 0 := by
      have h8 : ∀ i : Fin n, a i = 0 := h10
      simp_all [Finset.sum_eq_zero]
    linarith [h3, hsum]
  · 
    have h3 : ∃ i : Fin n, a i > 0 := by 
      by_contra h7
      push_neg at h7
      have h4 : ∀ i : Fin n, a i = 0 := by
        intro i
        have h5 : a i ≤ 0 := by linarith [h7 i]
        have h6 : a i ≥ 0 := ha i
        linarith
      have h10' : ∀ i : Fin n, a i = 0 := h4
      tauto
    rcases h3 with ⟨i, hi⟩
    have eq3 : ((i.1 + 1 : ℝ) - b) ^ 2 * a i = 0 := h2 i
    have eq4 : ((i.1 + 1 : ℝ) - b) ^ 2 = 0 := by
      nlinarith
    have eq5 : (i.1 + 1 : ℝ) - b = 0 := by
      apply pow_eq_zero 
      exact eq4
    have eq6 : b = (i.1 + 1 : ℝ) := by linarith
    refine ⟨(i.1 + 1 : ℤ), by
      simp [eq6]⟩