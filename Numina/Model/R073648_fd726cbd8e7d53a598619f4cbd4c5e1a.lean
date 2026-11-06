import Mathlib

open Real

theorem algebra_175070 {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ x, f 0 x = 2 * cos x)
    (hfn : ∀ n x, f (n + 1) x = 4 / (2 - f n x)) :
    f 2023 (π / 3) = 4 := by
  have h1 : f 0 (π / 3) = 1 := by
    rw [hf0]
    have hcos : cos (π / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [hcos]
    norm_num
  have h2 : f 1 (π / 3) = 4 := by
    rw [hfn 0 (π / 3), h1]
    norm_num
  have h3 : f 2 (π / 3) = -2 := by
    rw [hfn 1 (π / 3), h2]
    norm_num
  have h4 : f 3 (π / 3) = 1 := by
    rw [hfn 2 (π / 3), h3]
    norm_num
  have h5 : ∀ k : ℕ, f (3 * k) (π / 3) = 1 ∧ f (3 * k + 1) (π / 3) = 4 ∧ f (3 * k + 2) (π / 3) = -2 := by
    intro k
    induction k with
    | zero =>
      constructor
      · exact h1
      constructor
      · exact h2
      · exact h3
    | succ k ih =>
      have h6 : f (3 * (k + 1)) (π / 3) = 1 := by
        have eq1 : 3 * (k + 1) = 3 * k + 3 := by ring
        rw [eq1]
        rw [hfn (3 * k + 2) (π / 3)]
        rw [ih.right.right]
        norm_num
      have h7 : f (3 * (k + 1) + 1) (π / 3) = 4 := by
        have eq2 : 3 * (k + 1) + 1 = (3 * (k + 1)) + 1 := by ring
        rw [eq2]
        rw [hfn (3 * (k + 1)) (π / 3)]
        rw [h6]
        norm_num
      have h8 : f (3 * (k + 1) + 2) (π / 3) = -2 := by
        have eq3 : 3 * (k + 1) + 2 = (3 * (k + 1) + 1) + 1 := by ring
        rw [eq3]
        rw [hfn (3 * (k + 1) + 1) (π / 3)]
        rw [h7]
        norm_num
      constructor
      · exact h6
      constructor
      · exact h7
      · exact h8
  have h674 := (h5 674).2.1
  norm_num at h674 ⊢
  exact h674