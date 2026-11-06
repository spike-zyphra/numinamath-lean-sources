import Mathlib
open Matrix
noncomputable section

def F : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem calculus_7245 {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A = !![1, 1; 1, 0]) :
    F 784 * F 786 - F 785 ^ 2 = -1 := by 
  have h1 : ∀ (n : ℕ), F (n + 2) * F n - F (n + 1) ^ 2 = (-1 : ℤ) ^ (n + 1) := by 
    intro n 
    induction n with 
    | zero =>
      simp [F] 
    | succ n ih =>
      simp [F] at ih ⊢ 
      all_goals 
        ring_nf at ih ⊢ 
        <;> try { 
          nlinarith 
        }
  have h4 : F 786 * F 784 - F 785 ^ 2 = (-1 : ℤ) ^ 785 := by 
    specialize h1 784 
    norm_num at h1 ⊢ 
    all_goals 
      linarith 
  have h5 : (-1 : ℤ) ^ 785 = -1 := by 
    norm_num 
  rw [h5] at h4 
  linarith