import Mathlib

theorem algebra_8957
    (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 1 / 4)
    (h₂ : ∀ n ≥ 2, a (n + 1) = (n - 1) * a n / (n - a n)) :
    ∀ n ≥ 1, a n = 1 / (3 * n - 2) := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    linarith
  | succ n ih => 
    cases n with
    | zero => -- n = 1
      rw [h₀]
      norm_num 
    | succ n => 
      cases n with
      | zero => -- n = 2
        rw [h₁]
        norm_num 
      | succ n => -- n >= 3
        have eq3 := ih (by linarith)
        have eq4 : (n + 2 : ℕ) ≥ 2 := by linarith
        have eq5 := h₂ (n + 2) eq4
        simp [show n + 2 + 1 = n + 3 by omega] at eq5 ⊢
        rw [eq5, eq3]
        field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
        <;> norm_num
        <;> field_simp
        <;> ring_nf
        <;> field_simp
        <;> ring_nf