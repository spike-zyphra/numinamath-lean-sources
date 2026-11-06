import Mathlib

theorem algebra_261430 {u : ℕ → ℤ} (hu012 : u 0 = 1 ∧ u 1 = 2 ∧ u 2 = 0)
    (hun : ∀ n ≥ 3, u n = 2 * u (n - 1) + u (n - 2) - 2 * u (n - 3)) :
    ∀ n, u n = 2 - 2 / 3 * (-1 : ℝ)^n - 1 / 3 * 2^n := by
  rcases hu012 with ⟨hu0, hu1, hu2⟩
  intro n
  have eq1 : ∀ (n : ℕ), u n = 2 - 2 / 3 * (-1 : ℝ)^n - 1 / 3 * 2^n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    match n with
    | 0 =>
      simp [hu0]
      all_goals norm_num [hu0]
      <;> linarith
    | 1 =>
      simp [hu1]
      all_goals norm_num [hu1]
      <;> linarith
    | 2 =>
      simp [hu2]
      all_goals norm_num [hu2]
      <;> linarith
    | n + 3 =>
      have eq2 : u (n + 3) = 2 * u (n + 2) + u (n + 1) - 2 * u n := by
        specialize hun (n + 3) (by omega)
        simpa using hun
      have h1 := ih (n + 2) (by omega)
      have h2 := ih (n + 1) (by omega)
      have h3 := ih (n) (by omega)
      simp [eq2, h1, h2, h3]
      <;> ring_nf
      <;> norm_num [Real.rpow_add]
      <;> tauto
  specialize eq1 n
  exact_mod_cast eq1
  all_goals norm_num
  all_goals try { nlinarith }
  all_goals norm_num [hu0, hu1, hu2]
  all_goals try { nlinarith }