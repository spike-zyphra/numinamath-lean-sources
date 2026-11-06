import Mathlib

theorem algebra_11518 {f : ℕ → ℝ} (hf : ∀ n, f n = n / 2 + 18 / n) :
    IsLeast {x | ∃ n, x = f n ∧ n > 0} (f 6) := by 
  constructor
  · -- First, show that f(6) is in the set.
    use 6
    all_goals
      norm_num [hf]
  · -- Now, show that f(6) is the least element in the set.
    intro x hx
    rcases hx with ⟨n, hfn, hn⟩
    have h1 : f 6 ≤ f n := by
      rw [hf 6, hf n]
      have h3 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast show (n : ℕ) > 0 from hn
      have h4 : (6 : ℝ) / 2 + 18 / (6 : ℝ) = (6 : ℝ) := by norm_num
      have h5 : (n : ℝ) / 2 + 18 / (n : ℝ) ≥ (6 : ℝ) := by
        have h3 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast show (n : ℕ) > 0 from hn
        have h6 : (n : ℝ) / 2 + 18 / (n : ℝ) - (6 : ℝ) ≥ 0 := by
          have h6 : (n : ℝ) / 2 + 18 / (n : ℝ) - (6 : ℝ) = ((n : ℝ) ^ 2 + 36 - 12 * (n : ℝ)) / (2 * (n : ℝ)) := by
            field_simp
            ring
          rw [h6]
          have h7 : (n : ℝ) ^ 2 + 36 - 12 * (n : ℝ) ≥ 0 := by
            nlinarith [sq_nonneg ((n : ℝ) - (6 : ℝ))]
          have h8 : 2 * (n : ℝ) > 0 := by
            nlinarith [show (n : ℝ) > 0 from h3]
          apply div_nonneg
          · linarith
          · linarith
        linarith
      linarith [h4, h5]
    have h2 : x = f n := hfn
    linarith [h2, h1]