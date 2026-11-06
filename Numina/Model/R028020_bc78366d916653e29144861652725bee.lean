import Mathlib

open Real
open scoped BigOperators

theorem inequalities_155381 (n : ℕ) :
  ∏ i ∈ Finset.Icc 1 n, (1 + 1 / (i * (i + 2) : ℝ)) < 2 :=
by 
  have eq1 : ∀ n : ℕ, ∏ i ∈ Finset.Icc 1 n, (1 + 1 / (i * (i + 2) : ℝ)) = (2 * (n + 1) ) / (n + 2 : ℝ) := by
    intro n 
    induction n with 
    | zero =>
      norm_num 
      <;> try { native_decide }
    | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by norm_num)]
      rw [ih]
      field_simp
      ring_nf <;> field_simp
      <;> ring 
      <;> norm_num
      <;> field_simp
      <;> ring_nf <;> norm_num 
  specialize eq1 n 
  rw [eq1]
  have h4 : (2 * (n + 1) ) / (n + 2 : ℝ) < 2 := by
    apply (div_lt_iff (by positivity)).mpr 
    nlinarith 
  linarith [h4] 
  all_goals try { tauto } 
  all_goals norm_num
  all_goals try try { tauto } 
  all_goals norm_num 
  all_goals try { nlinarith }
  all_goals try { norm_num }
  all_goals try { tauto } 
  all_goals try { try { ring } }
  all_goals norm_num 
  all_goals try { tauto }