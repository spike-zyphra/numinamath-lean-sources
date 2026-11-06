import Mathlib

/-- In a confectionery shop, there were either overweight people or sweet-tooth lovers (possibly both). It turned out that $80\%$ of overweight people love sweets, and $70\%$ of sweet-tooth lovers are overweight. What portion of the attendees love sweets but are not overweight?-/
theorem logic_nd_puzzles_4216 (People : Type*) [Fintype People] [DecidableEq People] (overweight : Finset People) (loveSweets : Finset People) (h : overweight ∪ loveSweets = ⊤) (h₁ : ((overweight ∩ loveSweets).card / overweight.card : ℚ≥0) = 80 / 100) (h₂ : ((loveSweets ∩ overweight).card / loveSweets.card : ℚ≥0) = 70 / 100) : (loveSweets \ overweight).dens = 12 / 47 := by
  -- Check the number of overweight people is not zero 
  have nnro0 : (overweight.card : ℚ≥0) ≠ 0 :=
    (div_ne_zero_iff (a := ((overweight ∩ loveSweets).card : ℚ≥0)).mp (by rw [h₁]; norm_num)).2
  -- Check the number of people that love sweets is not zero 
  have nnrl0 : (loveSweets.card : ℚ≥0) ≠ 0 :=
    (div_ne_zero_iff (a := ((loveSweets ∩ overweight).card : ℚ≥0)).mp (by rw [h₂]; norm_num)).2
  have ro0 : (overweight.card : ℚ) ≠ 0 :=
    NNRat.coe_inj.not.mpr nnro0
  have rl0 : (loveSweets.card : ℚ) ≠ 0 :=
    NNRat.coe_inj.not.mpr nnrl0
  have nnrp0 : 0 < (Fintype.card People : ℚ≥0) := by
    simp
    norm_cast at nnro0
    exact (Nat.pos_of_ne_zero nnro0).trans_le (Finset.card_le_card (Finset.subset_univ _))
  -- the number of people who love sweets but not overweight equal the number of 
  -- people who love sweets sub the number of people who love sweets and overwight.
  have : (loveSweets \ overweight).dens = loveSweets.dens - (loveSweets ∩ overweight).dens := by
    rw [← Finset.dens_inter_add_dens_sdiff loveSweets overweight, add_tsub_cancel_left]
  rw [this, Finset.dens, Finset.dens, tsub_eq_iff_eq_add_of_le (by rw [div_le_div_right (lt_of_le_of_ne (zero_le _) nnrp0.ne), Nat.cast_le]; exact Finset.card_le_card Finset.inter_subset_left)]
  rw [Finset.inter_comm] at h₂ ⊢
  rw [← NNRat.coe_inj] at h₁ h₂ ⊢
  push_cast at h₁ h₂ ⊢
  simp [Finset.card_inter, h, div_eq_iff, ro0, rl0] at h₁ h₂ ⊢
  -- the number of all people less than or equal the number of people who 
  -- overwight add the number of people who love sweets.  
  have hc : Fintype.card People ≤ overweight.card + loveSweets.card := by
    convert Finset.card_union_le _ _
    rw [h]
    rfl
  simp [Nat.cast_sub, hc] at h₁ h₂ ⊢
  have co : overweight.card = 5 * (Fintype.card People - loveSweets.card : ℚ) := by
    rw [sub_eq_iff_eq_add, ← eq_sub_iff_add_eq, add_comm (_ * _), ← sub_add_eq_add_sub, ← sub_eq_iff_eq_add] at h₁
    ring_nf at h₁
    field_simp at h₁
    rw [h₁]
    ring
  rw [co, ← sub_eq_zero] at h₂ ⊢
  ring_nf at h₂
  rw [add_eq_zero_iff_eq_neg] at h₂
  ring_nf at h₂
  rw [← eq_div_iff_mul_eq (by decide)] at h₂
  rw [h₂]
  field_simp
  ring