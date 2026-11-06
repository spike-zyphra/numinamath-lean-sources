import Mathlib


/- Given that x and y are distinct nonzero real numbers such that x + 2/x = y + 2/y, what is xy? -/
theorem algebra_95701 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (h : x + 2 / x = y + 2 / y) :
x * y = 2 := by
  -- we move everything to one side
  apply congr_arg (fun z => z - y - 2/y) at h
  ring_nf at h
  -- we can simplify this
  have h2: x + x⁻¹ * 2 + (-y - y⁻¹ * 2) = (x-y)*(1-2/(x*y)) := by
    ring_nf
    rw [mul_inv_cancel₀ (by assumption), mul_assoc x⁻¹, mul_inv_cancel₀ (by assumption)]
    ring_nf
  rw [h] at h2
  -- now we have 0 = something * something so one of them must be zero
  simp at h2

  cases' h2 with h3 h4
  · -- x-y = 0 gives contradiction with hxy
    apply congr_arg (fun z => z + y) at h3
    ring_nf at h3; tauto
  · -- 1 - 2/(x*y) = 0 gives xy by doing a bit of work which solves the problem
    apply congr_arg (fun z => (z + 2/(x*y))*x*y) at h4
    ring_nf at h4;
    rw [mul_comm, mul_assoc, mul_assoc y, mul_inv_cancel₀ (by assumption), mul_one, ← mul_assoc, mul_inv_cancel₀ (by assumption), one_mul, mul_comm] at h4;
    assumption