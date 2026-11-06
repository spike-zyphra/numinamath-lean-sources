import Mathlib

open Real

theorem number_theory_304352 (A B : Fin 2 → ℝ) (hA : A = ![√1998, 0])
    (hB : B = ![0, √2000]) : {P : Fin 2 → ℝ | ∃ a b : ℚ, P =
    ![↑a, ↑b] ∧ P ∈ segment ℝ A B} = ∅ := by
  simp [Set.ext_iff, segment]; intro P a b hP t tpos s spos hst h
  simp [hA, hB, hP, funext_iff] at h
  have h' := h 1; simp at h'; replace h := h 0; simp at h
  let ha := h; let hb := h'; rw [← eq_sub_iff_add_eq] at hst
  rw [hst] at ha; rw [← eq_div_iff] at hb; rw [hb] at ha
  apply_fun fun t => t ^ 2 at ha
  rw [mul_pow, sub_sq, sq_sqrt, div_pow, sq_sqrt] at ha
  norm_num at ha
  replace ha : b / √2000 = 1 / 2 * (b ^ 2 / 2000 + 1 - a ^ 2 / 1998) := by
    linarith only [ha]
  rw [one_div_mul_eq_div, div_eq_div_iff_comm, div_eq_iff, sqrt_eq_iff_eq_sq] at ha
  norm_cast at ha; obtain ⟨k, hk⟩ : IsSquare 2000 := by
    rw [← Rat.isSquare_natCast_iff]; push_cast
    use 2 / (b ^ 2 / 2000 + 1 - a ^ 2 / 1998) * b
    nth_rw 1 [ha]; ring
  rw [← pow_two] at hk
  have : k ^ 2 < 45 ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this
  have : 44 ^ 2 < k ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this; any_goals omega
  any_goals positivity
  rw [← ha]; positivity
  simp; intro beq0; simp [beq0] at h' hP
  simp [h'] at hst; simp [hst] at h
  obtain ⟨l, hl⟩ : IsSquare 1998 := by
    rw [← Rat.isSquare_natCast_iff]; push_cast
    rw [sqrt_eq_iff_eq_sq] at h; norm_cast at h
    use a; rw [h]; ring; simp
    rw [← h]; positivity
  rw [← pow_two] at hl
  have : l ^ 2 < 45 ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this
  have : 44 ^ 2 < l ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this; all_goals omega