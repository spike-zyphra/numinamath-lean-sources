import Mathlib

open Finset Real

theorem algebra_183691 {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x ∧ x ≤ 1 / 2 → f x = x + 1 / 2)
    (hf' : ∀ x, 1 / 2 < x ∧ x ≤ 1 → f x = 2 * (1 - x)) :
    f^[2006] (2 / 15) = 19 / 30 := by
  have h1 : f (2 / 15 : ℝ) = 19 / 30 := by
    specialize hf (2 / 15 : ℝ) ⟨by norm_num, by norm_num⟩
    rw [hf]
    norm_num
  have h5' : f^[5] (2 / 15 : ℝ) = (2 / 15 : ℝ) := by
    norm_num [Function.iterate_succ_apply', hf, hf']
    <;> norm_num 
    <;> try { linarith } 
    <;> norm_num [hf, hf']
    all_goals try { try { tauto } <;> try { linarith } }
  have h2006 : f^[2006] (2 / 15 : ℝ) = f (2 / 15 : ℝ) := by
    have h5 : ∀ (n : Nat), f^[5 * n + 1] (2 / 15 : ℝ) = f (2 / 15 : ℝ) := by
      intro n 
      induction n with 
      | zero => 
        norm_num [Function.iterate_succ_apply']
      | succ n ih =>
        have eq1 : f^[5 * (n + 1) + 1] (2 / 15 : ℝ) = f^[5 * n + 1 + 5] (2 / 15 : ℝ) := by
          ring_nf 
        have eq2 : f^[5 * n + 1 + 5] (2 / 15 : ℝ) = f^[5 * n + 1] (f^[5] (2 / 15 : ℝ)) := by
          rw [Function.iterate_add_apply]
        rw [eq1, eq2, h5'] 
        all_goals try { 
          rw [ih] 
          all_goals norm_num [Function.iterate_succ_apply', hf, hf']
          <;> try { linarith } 
        }
    specialize h5 401 
    have eq1 : (5 * (401 : Nat) + 1 : Nat) = (2006 : Nat) := by 
      norm_num 
    have h5_rw : f^[5 * (401 : Nat) + 1] (2 / 15 : ℝ) = f (2 / 15 : ℝ) := h5
    rw [eq1] at h5_rw 
    try { 
      exact_mod_cast h5_rw 
    }
    all_goals try { tauto }
  rw [h2006]
  all_goals try { 
    rw [h1] 
    all_goals norm_num
  }
  all_goals try { tauto }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { linarith }