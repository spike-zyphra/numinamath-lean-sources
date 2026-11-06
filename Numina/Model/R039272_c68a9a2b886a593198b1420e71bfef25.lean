import Mathlib

theorem algebra_122981 (n : ℕ) (x : Fin n → ℤ) (hx : ∀ i, x i = -2 ∨ x i = 0 ∨ x i = 1)
    (hsum : ∑ i, x i = -17) (hsumsq : ∑ i, (x i)^2 = 37) :
    (∑ i, (x i)^3)^2 = 5041 := by

  have eq3 : (∑ i, (x i) ^ 3) = -71 := by
    have h3 : ∀ i : Fin n, (x i) ^ 3 = - (x i) ^ 2 + 2 * (x i) := by
      intro i
      have h2' : (x i : ℤ) = -2 ∨ (x i : ℤ) = 0 ∨ (x i : ℤ) = 1 := hx i
      rcases h2' with (h | h | h)
      · -- x i = -2
        rw [h]
        norm_num
      · -- x i = 0
        rw [h]
        norm_num
      · -- x i = 1
        rw [h]
        norm_num

    have h4 : ∑ i, (x i) ^ 3 = - ∑ i, (x i) ^ 2 + 2 * (∑ i, (x i)) := by
      calc
        ∑ i, (x i) ^ 3 = ∑ i, (-(x i) ^ 2 + 2 * (x i)) := by
          apply Finset.sum_congr
          · -- Show that the index set is the same
            rfl
          · -- Show that the terms are equal
            intro i _
            specialize h3 i
            linarith [h3]
        _ = ∑ i, (-(x i) ^ 2) + ∑ i, (2 * (x i)) := by
          rw [Finset.sum_add_distrib]
        _ = - (∑ i, (x i) ^ 2) + ∑ i, (2 * (x i)) := by
          simp [Finset.sum_neg_distrib]
        _ = - (∑ i, (x i) ^ 2) + 2 * (∑ i, (x i)) := by
          simp [Finset.mul_sum]

    rw [h4]
    rw [hsumsq, hsum]
    all_goals norm_num

  rw [eq3]
  all_goals norm_num