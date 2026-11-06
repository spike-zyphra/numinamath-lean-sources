import Mathlib

theorem number_theory_237492 (p : ℕ → ℝ) (h₀ : ∀ m n, p (m + n) = p m + p n + m * n)
    (h₁ : p 1 = 1) :
    ∃ r, p r = 2016 := by
  have h2 : ∀ (n : ℕ), p n = (↑n * (↑n + 1)) / 2 := by
    intro n 
    induction n with
    | zero =>
      have h1 : p 0 = 0 := by
        specialize h₀ 0 0
        norm_num at h₀ ⊢
        <;> linarith
      simp [h1]
      <;> linarith
    | succ n ih =>
      have eq1 : p (n + 1) = p n + p 1 + (↑n * (1 : ℝ)) := by
        specialize h₀ n 1
        simpa using h₀
      rw [eq1, h₁, ih]
      field_simp
      <;> ring_nf <;> norm_num
      <;> nlinarith
  use 63 
  specialize h2 63 
  norm_num at h2 ⊢
  all_goals linarith