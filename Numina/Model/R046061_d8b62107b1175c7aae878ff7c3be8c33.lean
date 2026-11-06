import Mathlib

open Finset

theorem number_theory_225345 {k : ℕ → ℕ} (hk : ∀ n, Odd n → k n = n)
    (hk' : ∀ n, Even n → k n = k (n / 2)) (f : ℕ → ℕ)
    (hf : ∀ n, f n = ∑ i ∈ Icc 1 n, k i) (n : ℕ) :
    f (2 * n) - f n = n ^ 2 := by
  have h1 : ∀ (i : ℕ), k (2 * i + 1) = 2 * i + 1 := by
    intro i
    have h2 : Odd (2 * i + 1) := by
      use i
      all_goals omega
    specialize hk (2 * i + 1) h2
    simpa using hk

  have h2 : ∀ i : ℕ, k (2 * i) = k i := by
    intro i
    have h3 : Even (2 * i) := by
      simp [Nat.even_mul]
    have hk3 : k (2 * i) = k ((2 * i) / 2) := by
      apply hk' 
      exact h3
    have h4 : (2 * i) / 2 = i := by
      omega
    rw [h4] at hk3
    exact hk3

  have h3 : f (2 * n) = f n + n ^ 2 := by
    rw [hf (2 * n), hf n]
    have h4 : ∀ (n : ℕ), ∑ i ∈ Icc 1 (2 * n), k i = ∑ i ∈ Icc 1 n, k i + n ^ 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring]
        rw [sum_Icc_succ_top (by linarith), sum_Icc_succ_top (by linarith)]
        have h3' : k (2 * n + 1) = 2 * n + 1 := by
          apply h1
        have h40 : k (2 * n + 2) = k (n + 1) := by
          have he : Even (2 * n + 2) := by 
            simp [Nat.even_add, Nat.even_mul]
          have hk20 : k (2 * n + 2) = k ((2 * n + 2) / 2) := by 
            apply hk' 
            exact he
          have hc : (2 * n + 2) / 2 = n + 1 := by omega
          rw [hc] at hk20 
          exact hk20 
        rw [h3', h40] 
        rw [ih] 
        simp [Finset.sum_Icc_succ_top] at *
        all_goals 
          ring_nf 
          <;> omega 
    specialize h4 n 
    simpa using h4 
  have h4 : f (2 * n) = f n + n ^ 2 := h3 
  have h5 : f (2 * n) ≥ f n := by
    omega
  omega