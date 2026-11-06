import Mathlib

theorem algebra_256076 {a : ℕ → ℝ} {d : ℝ} (ha : ∀ n, a n = a 0 + d * n)
    (m : ℕ) (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i ∈ Finset.range m, a (n * m + i)) :
    ∃ d, ∀ n, S (n + 1) = S n + d := by
  use m^2 * d
  intro n
  have eq1 : S (n + 1) = ∑ i ∈ Finset.range m, a ((n + 1) * m + i) := by
    specialize hS (n + 1)
    simpa using hS
  have eq2 : S n = ∑ i ∈ Finset.range m, a (n * m + i) := by
    specialize hS n
    simpa using hS
  rw [eq1, eq2]
  have h1 : ∀ i, a ((n + 1) * m + i) = a (n * m + i) + m * d := by 
    intro i 
    rw [ha ((n + 1) * m + i), ha (n * m + i)]
    simp [mul_add, add_mul]
    ring
  have h2 : ∑ i ∈ Finset.range m, a ((n + 1) * m + i) = ∑ i ∈ Finset.range m, a (n * m + i) + m^2 * d := by
    rw [Finset.sum_congr rfl (fun i hi => h1 i)]
    simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    <;> ring
  linarith [h2]