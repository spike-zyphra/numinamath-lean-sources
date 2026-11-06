import Mathlib

open Finset Real

theorem number_theory_319871 {p : ℕ → ℕ} (hp : ∀ n, Odd (p n) ∧ p n ∣ n ∧ ∀ m, Odd m → m ∣ n → m ≤ p n) :
    ∀ n, 0 < n → |∑ i ∈ Icc 1 n, (p i : ℝ) / i - 2 / 3 * n| < 1 := by
  have h1 := hp 0
  have h52 : (p 0 + 2 : ℕ) ∣ 0 := by 
    norm_num
  have h21 : Odd (p 0) := h1.1
  have h51 : Odd (p 0 + 2 : ℕ) := by 
    have h11 : Odd (p 0) := h1.1
    rcases h11 with ⟨k, hk⟩
    use k + 1
    simp [hk]
    all_goals omega
  have h5 := h1.2.2 (p 0 + 2)
  have h53 := h5 h51 h52
  omega