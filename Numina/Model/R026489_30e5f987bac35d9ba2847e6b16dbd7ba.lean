import Mathlib

open Finset

theorem algebra_906 {n : ℕ} (hn : Odd n) (a : ℕ → ℤ) (ha : ∀ i ∈ range n, a i < 0)
    (hdist : ∀ i ∈ range n, ∀ j ∈ range n, i ≠ j → a i ≠ a j) :
    ∃ k, 0 < k ∧ ∏ i ∈ range n, (i + 1 - 1 / a i : ℝ) = k := by

  have h1 : ∏ i in range n, ((i + 1 : ℝ) - (1 / (a i : ℝ))) > (0 : ℝ) := by
    have h6 : ∀ i : ℕ, i ∈ range n → ((i + 1 : ℝ) - (1 / (a i : ℝ)) ) > 0 := by
      intro i hi
      have h18 : a i < 0 := by 
        apply ha i hi
      have h10 : (a i : ℝ) < (0 : ℝ) := by exact_mod_cast h18
      have h11 : (1 / (a i : ℝ) ) < (0 : ℝ) := by 
        apply div_neg_of_pos_of_neg
        · norm_num
        all_goals nlinarith
      have h3 : ((i + 1 : ℝ) - (1 / (a i : ℝ)) ) > (0 : ℝ) := by
        have h7 : (i + 1 : ℝ) > 0 := by positivity
        linarith 
      simpa using h3

    apply Finset.prod_pos
    intro i hi 
    exact h6 i hi

  refine' ⟨∏ i in range n, ((i + 1 : ℝ) - (1 / (a i : ℝ))), h1, rfl⟩