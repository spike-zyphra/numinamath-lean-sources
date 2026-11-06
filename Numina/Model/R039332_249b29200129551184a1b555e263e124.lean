import Mathlib

theorem number_theory_97620 {f : ℕ → ℕ}
(hf1 : f 1 = 2)
(hfn : ∀ n, Even n → f n = f (n - 1) + 1)
(hfn' : ∀ n, Odd n → n > 1 → f n = f (n - 2) + 2) :
f 2017 = 2018 := by
  have h1 : ∀ (n : ℕ), f (2 * n + 1) = 2 * n + 2 := by
    intro n
    induction n with
    | zero =>
      simp [hf1]
    | succ n ih =>
      have eq1 : f (2 * (n + 1) + 1) = f (2 * n + 1) + 2 := by
        have h2 : (2 * (n + 1) + 1 : ℕ) = (2 * n + 1 + 2 : ℕ) := by
          omega
        rw [h2]
        have h3 : Odd (2 * n + 1 + 2 : ℕ) := by
          simp [Nat.odd_iff]
          <;> omega
        have h4 : (2 * n + 1 + 2 : ℕ) > 1 := by
          omega
        have eq2 := hfn' (2 * n + 1 + 2) h3 h4
        have eq3 : (2 * n + 1 + 2 - 2 : ℕ) = (2 * n + 1 : ℕ) := by
          omega
        simp [eq3] at eq2 ⊢
        all_goals omega
      rw [eq1]
      rw [ih]
      all_goals omega
  have h2 : 2017 = 2 * 1008 + 1 := by
    omega
  rw [h2]
  specialize h1 1008
  exact h1