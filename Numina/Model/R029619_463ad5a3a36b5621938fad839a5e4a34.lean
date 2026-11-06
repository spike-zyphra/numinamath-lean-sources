import Mathlib

theorem algebra_109267 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) (h : ∑ i, 1 / a i ≠ 0) (S : ℝ)
    (hS : S = ∑ i, a i) (hS1 : S = -2020) :
    ∑ i, (x + S - a i) / a i = -n ↔ x = 2020 := by
  constructor
  · -- Assume $\sum_i \frac{x + S - a_i}{a_i} = -n$, prove $x = 2020$
    intro h_eq

    have eq1 : ∀ i, (x + S - a i) / a i = (x + S) / a i - 1 := by
      intro i
      have h1 : a i ≠ 0 := ha i
      field_simp

    have eq2 : ∑ i, (x + S - a i) / a i = ∑ i, ((x + S) / a i - 1) := by
      apply Finset.sum_congr
      · rfl
      · intro i _
        exact eq1 i

    have eq3 : ∑ i, ((x + S) / a i - 1) = (∑ i, ((x + S) / a i)) - n := by
      calc
        ∑ i, ((x + S) / a i - 1) = ∑ i, ((x + S) / a i) - ∑ i, (1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ i, ((x + S) / a i) - (n : ℝ) := by
          simp [Finset.sum_const, Finset.card_univ]

    have eq4 : ∑ i, ((x + S) / a i) = 0 := by
      linarith [eq2, eq3, h_eq]

    have eq5 : ∑ i, ((x + S) / a i) = (x + S) * (∑ i, (1 / a i)) := by
      have h6 : ∀ i, ((x + S) / a i) = (x + S) * (1 / a i) := by
        intro i
        have h1 : a i ≠ 0 := ha i
        field_simp

      calc
        ∑ i, ((x + S) / a i) = ∑ i, ((x + S) * (1 / a i) ) := by
          apply Finset.sum_congr
          . rfl
          intro i _
          exact h6 i
        _ = (x + S) * (∑ i, (1 / a i)) := by
          rw [Finset.mul_sum]

    rw [eq5] at eq4

    have h1 : (x + S) = 0 := by
      apply (mul_left_inj' (show (∑ i, (1 / a i)) ≠ 0 by exact h)).mp
      linarith

    have h2 : x = -S := by linarith

    rw [h2]
    have h3 : (S : ℝ) = -2020 := hS1
    rw [h3]
    all_goals norm_num

  · -- Assume $x = 2020$, prove $\sum_i \frac{x + S - a_i}{a_i} = -n$
    intro h_eq
    rw [h_eq] 
    have eq1 : S = -2020 := hS1

    have eq2 : ∑ i, ((2020 : ℝ) + S - a i) / a i = -n := by

      have eq3 : ∀ i, ((2020 : ℝ) + S - a i) / a i = -1 := by
        intro i
        have h10 : a i ≠ 0 := ha i
        have h11 : (2020 : ℝ) + S = (0 : ℝ) := by
          linarith [eq1]
        have h12 : ((2020 : ℝ) + S - a i) = -a i := by
          calc
            ((2020 : ℝ) + S - a i) = ((2020 : ℝ) + S) - a i := by ring
            _ = (0 : ℝ) - a i := by rw [h11]
            _ = -a i := by ring

        rw [h12]
        have h10 : a i ≠ 0 := ha i
        field_simp [h10]
  
      calc
        ∑ i, ((2020 : ℝ) + S - a i) / a i = ∑ i, (-1 : ℝ) := by
          apply Finset.sum_congr
          · rfl
          intro i _
          exact eq3 i
        _ = ( - (n : ℝ) ) := by
          simp [Finset.sum_const, Finset.card_univ]
          all_goals linarith
        _ = -n := by
          linarith

    simpa using eq2