import Mathlib

theorem algebra_247963 {f : ℕ → ℝ} (hf1 : f 1 = 1) (hf2 : f 2 = 3)
    (hfn : ∀ n ≥ 3, 2 * f (n - 2) + f (n - 1) = f n) :
    ∀ n : ℕ, n ≥ 1 → f n = (2 ^ (n + 1) + (-1) ^ n) / 3 := by 
  intro n hn 
  induction' n using Nat.strongRecOn with n ih 
  cases n with 
  | zero => 
    exfalso 
    linarith
  | succ n => 
    cases n with 
    | zero => 
      rw [hf1]
      norm_num 
    | succ n => 
      cases n with 
      | zero => 
        rw [hf2]
        norm_num 
      | succ n => 
        have eq1 := hfn (n + 3) (by omega)
        simp [show n + 3 = (n + 3 : ℕ) by rfl] at eq1 
        have h1 := ih (n + 2) (by omega)
        have h2 := ih (n + 1) (by omega)
        simp [h1, h2] at eq1 ⊢ 
        ring_nf at eq1 ⊢ 
        <;> linarith [eq1]