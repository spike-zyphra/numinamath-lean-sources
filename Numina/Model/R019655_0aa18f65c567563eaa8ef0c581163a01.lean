import Mathlib

def is_rootiful (S : Set ℤ) : Prop :=
  ∀ n > 0, ∀ a : Fin (n + 1) → ℤ,
    (∀ i, a i ∈ S) → ∀ x : ℤ, ∑ i : Fin (n + 1), a i * x ^ i.val = 0 → x ∈ S

theorem number_theory_30224 (S : Set ℤ) :
    (is_rootiful S ∧ ∀ a b : ℕ, a > 0 → b > 0 → (2 ^ a - 2 ^ b) ∈ S) ↔
    S = ⊤ := by 
  constructor
  · -- Assume the conjunction 
    intro h 
    rcases h with ⟨hS, h2⟩
    have h0 : (0 : ℤ) ∈ S := by 
      have h01 := h2 1 1 (by norm_num) (by norm_num)
      norm_num at h01 ⊢ 
      all_goals tauto 
    have h1 : ∀ x : ℤ, x ∈ S := by
      intro x 
      have h3 := hS 1 (by norm_num) (fun i : Fin (1 + 1) => 
          (0 : ℤ)
        )
      have h4 : (∀ i : Fin (1 + 1), (fun (j : Fin (1 + 1)) => (0 : ℤ)) i ∈ S) := by 
        intro i 
        fin_cases i <;> simp [h0]
      have h32 := h3 h4 x (by 
          simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        )
      exact h32 
    ext x
    simp [h1]
  · -- Now back for the reverse direction 
    intro h 
    rw [h]
    constructor
    · -- Show that S is rootiful
      intro n hn a ha x hx
      simp at ha hx ⊢
      all_goals
        aesop
    · -- Show that all differences of powers of 2 are in S
      intro a b ha hb 
      simp
      all_goals
        try { tauto }
        <;> try { linarith }