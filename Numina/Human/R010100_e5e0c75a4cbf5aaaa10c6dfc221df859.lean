import Mathlib

open Real
open scoped BigOperators

/- Find the least positive integer n such that
1/(sin45∘ * sin46∘) + 1/(sin47∘ * sin48∘) + ... + 1/(sin133∘ * sin134∘)= 1 / sin n∘.
-/
theorem algebra_97404 {deg : ℝ} (hdeg : deg = π / 180) :
∑ i ∈ Finset.range 45, (1 / (sin ((2 * i + 45) * deg) * sin ((2 * i + 46) * deg))) =
1 / sin (deg) := by
  -- We rewrite the body of the sum using the angle-difference trig identity
  have h_trig : forall k, 0 < k -> k < 178 -> 1 / (sin (k * deg) * sin ((k + 1) * deg)) = 1 / sin (1 * deg) * (cot (k * deg) - cot ((k + 1) * deg)) := by
    intro k
    intros hk_l hk_u

    have h := sin_sub ((k + 1) * deg) (k * deg)
    conv at h => lhs; ring_nf

    have hsink_lt : forall k, 0 < k -> k < 179 -> sin (k * deg) ≠ 0 := by
      intros k hk_l hk_u
      suffices 0 < sin (k * deg) by linarith
      rw [hdeg]
      apply sin_pos_of_pos_of_lt_pi
      · field_simp
      · apply lt_trans
        apply mul_lt_mul_of_pos_right hk_u
        linarith [pi_pos]
        linarith [pi_pos]

    have hsin1 := hsink_lt 1 (by linarith) (by linarith)
    simp at hsin1

    calc
      1 / (sin (k * deg) * sin ((k + 1) * deg))
        = 1 / sin deg * sin deg / (sin (k * deg) * sin ((k + 1) * deg)) := by field_simp
      _ = 1 / sin deg * sin ((k + 1) * deg - k * deg) / (sin (k * deg) * sin ((k + 1) * deg)) := by congr; ring
    clear hsin1

    conv =>
      left
      rw [mul_div_assoc]
      arg 2
      rw [sin_sub, sub_div]
    -- We can rewrite the sin and cos terms into cotangents for easier manipulation
    congr 2
    · simp
    · have hsink := hsink_lt (k + 1) (by linarith) (by linarith)
      rw [mul_comm, mul_div_mul_right _ _ hsink]
      exact Eq.symm (cot_eq_cos_div_sin _)
    · have hsink := hsink_lt k (by linarith) (by linarith)
      rw [mul_comm, mul_div_mul_left _ _ hsink]
      exact Eq.symm (cot_eq_cos_div_sin _)

  -- We verify that the trig identity holds for all k in the sum's range
  have h_telescope_spec : ∀ k ∈ Finset.range 45,
    1 / (sin ((2 * k + 45) * deg) * sin ((2 * k + 45 + 1) * deg))
    = 1 / sin (1 * deg) * (cot ((2 * k + 45) * deg) - cot ((2 * k + 45 + 1) * deg))
  := by
    intro k
    intros k_bound
    rw [h_trig]
    · linarith
    · rw [Finset.mem_range] at k_bound
      norm_cast
      linarith
  clear h_trig
  
  conv =>
    left
    enter [2, i, 2]
    norm_cast
    enter [2, 1, 1, 1]
    rw [Nat.add_succ, Nat.succ_eq_add_one]

  norm_cast at h_telescope_spec
  rw [Finset.sum, Multiset.map_congr (Eq.refl _) h_telescope_spec, <-Finset.sum]
  clear h_telescope_spec
  rw [<- Finset.mul_sum]
  suffices ∑ i ∈ Finset.range 45, (cot ((2 * i + 45) * deg) - cot ((2 * i + 45 + 1) * deg)) = 1 by
    norm_cast at this
    rw [this]
    simp
  
  -- We use the fact that cot(x) = - cot(180 - x) to cancel out most of the terms
  have cot_sym : ∀ k, cot (k * deg) = - cot ((180 - k) * deg) := by
    intro k
    rw [hdeg, sub_mul]
    conv =>
      right
      enter [1, 1, 1]
      rw [mul_div_cancel₀ _ (by linarith)]
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    simp
    field_simp
  
  have cot_sym_45 := fun k => cot_sym (k + 45)
  have cot_sym_46 := fun k => cot_sym (k + 45 + 1)
  unfold Finset.sum
  simp
  -- rewrite the first half of the terms
  iterate 22 rw [cot_sym_45, cot_sym_46]
  ring_nf

  rw [hdeg, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
  rw [show π / 180 * 90 = π / 2 by field_simp; linarith]
  rw [show π / 180 * 45 = π / 4 by field_simp; linarith]
  simp