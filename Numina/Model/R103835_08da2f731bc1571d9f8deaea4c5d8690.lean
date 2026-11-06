import Mathlib

open Real

theorem algebra_229217 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (A1 A2 A3 : ℝ) (hA1 : A1 ≠ A2) (hA2 : A2 ≠ A3) (hA3 : A3 ≠ A1)
    (k1 : ℝ) (hk1 : k1 = deriv f A1) (kij : ℝ → ℝ → ℝ)
    (hkij : ∀ i j, kij i j = (f i - f j) / (i - j)) :
    k1 = kij A1 A2 + kij A1 A3 - kij A2 A3 := by
  rcases hf with ⟨a, b, c, h_def⟩
  have f_eq : f = fun x => a * x ^ 2 + b * x + c := h_def
  have k12 : kij A1 A2 = a * (A1 + A2) + b := by
    rw [hkij]
    have h1' : A1 - A2 ≠ 0 := by
      intro h
      apply hA1
      linarith
    field_simp [h1']
    ring_nf
    <;> simp [f_eq]
    <;> ring
  have k13 : kij A1 A3 = a * (A1 + A3) + b := by
    rw [hkij]
    have h1' : A1 - A3 ≠ 0 := by
      intro h
      apply hA3
      linarith
    field_simp [h1']
    ring_nf
    <;> simp [f_eq]
    <;> ring
  have k23 : kij A2 A3 = a * (A2 + A3) + b := by
    rw [hkij]
    have h1' : A2 - A3 ≠ 0 := by
      intro h
      apply hA2
      linarith
    field_simp [h1']
    ring_nf
    <;> simp [f_eq]
    <;> ring
  have k1_eq : k1 = 2 * a * A1 + b := by
    rw [hk1, f_eq]
    simp [deriv_pow, deriv_mul, deriv_id', mul_comm b, mul_assoc]
    all_goals field_simp
    <;> ring
  rw [k1_eq, k12, k13, k23]
  <;> ring