import Mathlib
open Real
theorem Other_24827
  (a b c d_a d_b d_c S S_a S_b S_c : ℝ)
  (IsCentroid : Prop)
  (h_sides_pos : 0 < a ∧ 0 < b ∧ 0 < c)
  (h_areas_nonneg : 0 ≤ S_a ∧ 0 ≤ S_b ∧ 0 ≤ S_c)
  (h_sa : S_a = a * d_a / 2)
  (h_sb : S_b = b * d_b / 2)
  (h_sc : S_c = c * d_c / 2)
  (h_S_sum : S = S_a + S_b + S_c)
  (h_centroid_iff_areas_eq : IsCentroid ↔ (S_a = S_b ∧ S_b = S_c)) :
  a * b * d_a * d_b + b * c * d_b * d_c + c * a * d_c * d_a ≤ 4 * S^2 / 3 ∧
  (a * b * d_a * d_b + b * c * d_b * d_c + c * a * d_c * d_a = 4 * S^2 / 3 ↔ IsCentroid) := by
  have ha_ne_zero := ne_of_gt h_sides_pos.1
  have hb_ne_zero := ne_of_gt h_sides_pos.2.1
  have hc_ne_zero := ne_of_gt h_sides_pos.2.2
  constructor
  · 
    calc
      a * b * d_a * d_b + b * c * d_b * d_c + c * a * d_c * d_a
      _ = 4 * (S_a * S_b + S_b * S_c + S_c * S_a) := by
        field_simp [h_sa, h_sb, h_sc, ha_ne_zero, hb_ne_zero, hc_ne_zero]
        ring
      _ ≤ 4 * (S_a + S_b + S_c)^2 / 3 := by
        rcases h_areas_nonneg  with ⟨ha, hb, hc⟩
        nlinarith [sq_nonneg (S_a - S_b), sq_nonneg (S_b - S_c), sq_nonneg (S_c - S_a),
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
      _ = 4 * S^2 / 3 := by
        rw [h_S_sum]
  · 
    have h_lhs_eq : a * b * d_a * d_b + b * c * d_b * d_c + c * a * d_c * d_a = 4 * (S_a * S_b + S_b * S_c + S_c * S_a) := by
        field_simp [h_sa, h_sb, h_sc, ha_ne_zero, hb_ne_zero, hc_ne_zero]; ring
    rw [h_lhs_eq, h_S_sum]
    have h_alg_iff : 4 * (S_a * S_b + S_b * S_c + S_c * S_a) = 4 * (S_a + S_b + S_c) ^ 2 / 3 ↔ S_a = S_b ∧ S_b = S_c := by
      constructor
      · 
        intro h_eq
        have h1 : (S_a - S_b) ^ 2 + (S_b - S_c) ^ 2 + (S_c - S_a) ^ 2 = 0 := by
          nlinarith 
        have h2 : (S_a - S_b) ^ 2 = 0 := by
          nlinarith [sq_nonneg (S_a - S_b), sq_nonneg (S_b - S_c), sq_nonneg (S_c - S_a)]
        have h3 : S_a = S_b := by
          nlinarith
        have h4 : (S_b - S_c) ^ 2 = 0 := by
          nlinarith [sq_nonneg (S_a - S_b), sq_nonneg (S_b - S_c), sq_nonneg (S_c - S_a)]
        have h5 : S_b = S_c := by
          nlinarith
        constructor
        · exact h3
        · exact h5
      · 
        rintro ⟨rfl, rfl⟩
        ring
    rw [h_alg_iff]
    rw [← h_centroid_iff_areas_eq]