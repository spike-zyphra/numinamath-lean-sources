import Mathlib

theorem algebra_13442 {a : ℕ → ℝ}
    (ha1 : a 1 = 1 / (2 ^ (2021) - 1))
    (ham : ∀ m > 0, a (m + 1) = 2 * a m + a 1) :
    a 2021 = 1 := by
  have h1 : ∀ n, a (n + 1) = (2 ^ (n + 1) - 1) * a 1 := by
    intro n
    induction n with
    | zero =>
      have eq1 : a (0 + 1) = a 1 := by 
        simp [show 0 + 1 = 1 by omega]
      have eq2 : (2 ^ (0 + 1) - 1 : ℝ) * a 1 = 1 * a 1 := by
        norm_num
      -- Two goals: show a 1 = a 1 and a 1 = a 1, trivial
      -- connect them
      linarith [eq1, eq2]
    | succ n ih =>
      have eq1 : a ((n + 1) + 1) = 2 * a (n + 1) + a 1 := ham (n + 1) (by linarith)
      rw [eq1]
      rw [ih]
      simp [pow_succ, mul_add, add_mul, mul_add, mul_assoc]
      <;> ring_nf <;> norm_num
      <;> simp [ha1]
      <;> ring_nf <;> norm_num
      <;> tauto
  have h2021 : a 2021 = (2 ^ 2021 - 1) * a 1 := by
    specialize h1 2020
    norm_num at h1 ⊢
    linarith
  rw [h2021]
  rw [ha1]
  field_simp
  <;> ring_nf <;> norm_num
  <;> try norm_num
  <;> try field_simp
  <;> try linarith