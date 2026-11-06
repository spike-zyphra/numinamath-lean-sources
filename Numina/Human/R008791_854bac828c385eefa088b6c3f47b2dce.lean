import Mathlib

/- Let $\omega$ be a complex number such that $\omega^7 = 1$ and $\omega \ne 1.$  Compute
\[\omega^{16} + \omega^{18} + \omega^{20} + \dots + \omega^{54}.\] -/
theorem algebra_12179 (ω : ℂ) (hω : ω^7 = 1 ∧ ω ≠ 1) :
    ∑ k ∈ Finset.range 20, ω^(2*k+16) = -1 := by
  -- Split the hypothesis
  obtain ⟨hω, ω_ne_1⟩ := hω

  -- Small change to use the geometric sum formula
  change ∑ k ∈ Finset.Ico 0 20, ω^(2*k+16) = -1
  have h (k : ℕ) : ω^(2*k+16) = ω^16*(ω^2)^k := by ring
  -- Rewrite h in the sum
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  -- Put ω^16 out of the sum
  rw [← Finset.mul_sum]

  -- ω^2 ≠ 1
  have hω2 : ω^2 ≠ 1 := by
    intro h
    -- If ω^2 = 1, then ω^6 = 1
    apply_fun (· ^ 3) at h
    simp [← pow_mul] at h
    rw [pow_succ] at hω
    -- Then we get ω = 1 from ω^6 = ω^7 = 1
    rw [h] at hω
    simp at hω
    contradiction

  -- Use the geometric sum formula
  rw [geom_sum_Ico hω2 (by simp)]

  -- Rewrite hω2 as ω^2 - 1 ≠ 0
  rw [← sub_ne_zero] at hω2
  -- Simplify the expression
  field_simp [hω2]
  ring_nf

  -- Simplify the expression
  rw [show ω^16 = (ω^7)^2*ω^2 by ring,
      show ω^56 = (ω^7)^8 by ring]
  rw [hω]
  ring
