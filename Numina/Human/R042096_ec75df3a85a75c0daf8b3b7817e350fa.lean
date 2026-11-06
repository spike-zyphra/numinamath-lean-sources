import Mathlib

open Real Set
open scoped BigOperators

/- 2. Solve the inequality $\frac{\sqrt{x}-6}{2-\sqrt{x+4}} \geq 2+\sqrt{x+4}$. -/
theorem inequalities_144685 (x : ℝ) (hx : 0 < x) :
    (sqrt x - 6) / (2 - sqrt (x + 4)) ≥ 2 + sqrt (x + 4) ↔ x ∈ Ioc 0 4 := by
  -- let's multiply by denominator
  constructor
  · intro h
    -- multiply by denominator (which is negative)
    apply (mul_le_mul_right (a:=-(2 - sqrt (x + 4))) (by
      simp
      refine lt_sqrt_of_sq_lt ?_
      norm_num; assumption
    )).mpr at h
    conv_rhs at h =>
      calc _
      _ = -(√x - 6) * ((2 - √(x + 4)) / (2 - √(x + 4))) := by ring_nf
      _ = 6 - √x := by rw [div_self (by apply ne_of_lt; simp; apply lt_sqrt_of_sq_lt; linarith)]; ring_nf;
    ring_nf at h
    rw [Real.sq_sqrt (by linarith)] at h
    ring_nf at h
    simp
    constructor
    · assumption
    · -- prepare and square both sides
      have h':√x≤6-x := by linarith
      have h2:= pow_le_pow_left₀ (by simp) h' 2
      have h3:0≤6-x := by linarith [sqrt_nonneg x]
      rw [Real.sq_sqrt (by linarith)] at h2; ring_nf at h2
      have h2:= add_le_add_left h2 (-x)
      ring_nf at h2
      -- we factor the quadratic
      conv_rhs at h2 =>
        calc _
        _ = (x - 4) * (x - 9) := by ring_nf
      apply mul_nonneg_iff.mp at h2
      -- now just casework
      cases' h2 with h2 h2
      · obtain ⟨hx, h2⟩ := h2
        linarith
      · obtain ⟨hx, h2⟩ := h2
        linarith
  · -- basically the same proof but in the other direction
    intro h
    obtain ⟨_, hx4⟩ := h
    simp
    apply (mul_le_mul_right (a:=-(2 - sqrt (x + 4))) (by
      simp
      refine lt_sqrt_of_sq_lt ?_
      norm_num; assumption
    )).mp
    conv_rhs =>
      calc _
      _ = -(√x - 6) * ((2 - √(x + 4)) / (2 - √(x + 4))) := by ring_nf
      _ = 6 - √x := by rw [div_self (by apply ne_of_lt; simp; apply lt_sqrt_of_sq_lt; linarith)]; ring_nf;
    ring_nf
    rw [Real.sq_sqrt (by linarith)]
    ring_nf
    suffices √x≤6-x by linarith
    refine (sqrt_le_left ?_).mpr ?_
    linarith
    suffices 0 ≤ -x + (6-x)^2 by linarith
    ring_nf
    conv_rhs =>
      calc _
      _ = (x - 4) * (x - 9) := by ring_nf
    apply mul_nonneg_iff.mpr
    right
    exact ⟨by linarith, by linarith⟩