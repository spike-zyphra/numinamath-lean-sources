import Mathlib

open Finset

theorem algebra_7385 {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ x, f 0 x = 1 / (1 - x))
    (hfn : ∀ n > 0, ∀ x, f n x = f 0 (f (n - 1) x)) :
    f 1976 1976 = 1976 := by 
  have f0_1976 : f 0 (1976 : ℝ) = 1 / (1 - 1976 : ℝ) := hf0 (1976 : ℝ)
  have f1_1976 : f 1 (1976 : ℝ) = 1975 / 1976 := by 
    rw [hfn 1 (by norm_num), hf0, f0_1976]
    norm_num
    <;> field_simp <;> norm_num
  -- f 2 1976 = 1976
  have f2_1976 : f 2 (1976 : ℝ) = 1976 := by 
    rw [hfn 2 (by norm_num), hf0, f1_1976]
    norm_num
    <;> field_simp
    <;> norm_num
  -- We then prove by induction that $f_{3k + 2}(1976) = 1976$ for all k : ℕ
  have h1 : ∀ k : ℕ, f (3 * k + 2) 1976 = 1976 := by
    intro k
    induction k with
    | zero =>
      norm_num [f2_1976]
    | succ k ih =>
      have eq1 : f (3 * (k + 1) + 2) 1976 = f (3 * k + 5) 1976 := by
        simp [mul_add, add_mul]
        <;> ring_nf <;> omega
      rw [eq1]
      -- f (3 * k + 5) 1976 = f 0 (f (3 * k + 4) 1976)
      have eq2 : f (3 * k + 5) 1976 = f 0 (f (3 * k + 4) 1976) := by 
        apply hfn
        all_goals omega
      -- f (3 * k + 4) 1976 = f 0 (f (3 * k + 3) 1976)
      have eq3 : f (3 * k + 4) 1976 = f 0 (f (3 * k + 3) 1976) := by 
        apply hfn
        all_goals omega
      -- f (3 * k + 3) 1976 = f 0 (f (3 * k + 2) 1976)
      have eq4 : f (3 * k + 3) 1976 = f 0 (f (3 * k + 2) 1976) := by 
        apply hfn
        all_goals omega
      -- f (3 * k + 2) 1976 = 1976 by induction hypothesis
      have eq5 : f (3 * k + 2) 1976 = 1976 := ih
      -- Substituting up the computation tree 
      rw [eq2, eq3, eq4, eq5]
      norm_num [hf0]
      <;> field_simp <;> norm_num
  -- Compute 1976 = 3 * 658 + 2
  have h2 : 1976 = 3 * (658 : ℕ) + 2 := by
    norm_num
  -- Final result using the inductive hypothesis
  rw [h2]
  apply h1
  all_goals norm_num
  all_goals try { tauto }
  all_goals try { norm_num }
  all_goals try { tauto }
  all_goals try { norm_num }
  all_goals try { tauto }