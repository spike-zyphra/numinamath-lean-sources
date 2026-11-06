import Mathlib

open Real

theorem algebra_98999 {φ ψ : ℝ} (hφ : φ = (1 + sqrt 5) / 2) (hψ : ψ = (1 - sqrt 5) / 2)
    (hφ1 : φ^2 = φ + 1) (hψ1 : ψ^2 = ψ + 1) (F : ℕ → ℝ)
    (hF : F 0 = 0 ∧ F 1 = 1 ∧ ∀ n, F (n + 2) = F (n + 1) + F n) :
    ∀ n, F n = (φ^n - ψ^n) / sqrt 5 := by

  rcases hF with ⟨hF0, hF1, hF2⟩
  intro n 
  have h1 : ∀ (n : ℕ), F n = (φ ^ n - ψ ^ n) / sqrt 5 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      rw [hF0]
      simp [hφ, hψ]
    | succ n =>
      cases n with 
      | zero =>
        rw [hF1]
        field_simp [hφ, hψ]
        <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      | succ n =>
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        simp [hF2 n, h2, h3] at *
        have eq1 : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
          have eq2 : φ ^ 2 = φ + 1 := hφ1
          calc
            φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
            _ = φ ^ n * (φ + 1) := by rw [eq2]
            _ = φ ^ n * φ + φ ^ n * 1 := by ring
            _ = φ ^ (n + 1) + φ ^ n := by ring
        have eq2 : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
          have eq3 : ψ ^ 2 = ψ + 1 := hψ1
          calc
            ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by ring
            _ = ψ ^ n * (ψ + 1) := by rw [eq3]
            _ = ψ ^ n * ψ + ψ ^ n * 1 := by ring
            _ = ψ ^ (n + 1) + ψ ^ n := by ring
        field_simp at *
        simp [eq1, eq2] at *
        <;> ring
  
  exact h1 n