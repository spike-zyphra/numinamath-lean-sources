import Mathlib

open Real

/- Terekhin D.A.

Let $1 < a ≤ b ≤ c$ Prove that

$$ log_a(b) + lob_b(c) + log_c(a) ≤ log_b(a) + log_c(b) + log_a(c) $$
 -/
theorem inequalities_193767 (a b c : ℝ) (ha : 1 < a) (hle : a ≤ b ∧ b ≤ c) :
    logb a b + logb b c + logb c a ≤ logb b a + logb c b + logb a c:= by

  obtain ⟨h2, h3⟩ := hle
  -- let x= Real.logb a b and y= Real.logb b c
  let q: ∃ x:ℝ, x = Real.logb a b := by
    use Real.logb a b
  obtain ⟨x, xdef⟩ := q
  let q: ∃ y:ℝ, y = Real.logb b c := by
    use Real.logb b c
  obtain ⟨y, ydef⟩ := q
  -- Then Real.logb c a = 1/(x*y)
  have h4: Real.logb c a = 1/(x*y) := by
    have h5:= Real.mul_logb (a:=b) (b:=c) (c:=a) (by linarith) (by linarith) (by linarith)
    rw [← Real.inv_logb a b] at h5
    apply congr_arg (fun x => (logb b c)⁻¹ * x) at h5
    rw [← mul_assoc, inv_mul_cancel₀ (by
      simp
      exact ⟨by linarith, ⟨by linarith, ⟨by linarith, ⟨by linarith, ⟨by linarith, by linarith⟩⟩⟩⟩⟩
    ), one_mul, ← xdef, ← ydef] at h5
    rw [h5]; ring_nf
  -- now we can convert this into equation in x and y
  rw [← Real.inv_logb a b, ← Real.inv_logb b c, ← Real.inv_logb c a, ← xdef, ← ydef, h4]; simp
  -- to make things simpler, we show that 0 < x, y
  have h6: 1 ≤ x := by
    rw [xdef]
    exact (le_logb_iff_rpow_le ha (by linarith)).mpr (by simp; linarith)
  have h7: 1 ≤ y := by
    rw [ydef]
    exact (le_logb_iff_rpow_le (by linarith) (by linarith)).mpr (by simp; linarith)

  -- let's move everything to one side
  suffices 0 ≤ x⁻¹ + y⁻¹ + x * y - x - y - x⁻¹ * y⁻¹ by linarith
  -- this factors
  conv_rhs =>
    calc x⁻¹ + y⁻¹ + x * y - x - y - x⁻¹ * y⁻¹
    _ = 1/x*(y/y) + 1/y*(x/x) + x * y*(x*y/(x*y)) - x*(x*y/(x*y)) - y*(x*y/(x*y)) - 1/(x*y) := by rw [div_self (by linarith), div_self (by linarith), div_self (by nlinarith)]; ring_nf
    _ = (x-1)*(y-1)*(x*y-1)/(x*y):= by ring_nf
  -- this is true since all of the terms are positive
  apply div_nonneg; apply mul_nonneg; apply mul_nonneg;
  rw [xdef]; simp; exact (le_logb_iff_rpow_le ha (by linarith)).mpr (by simp; linarith)
  linarith
  nlinarith
  nlinarith