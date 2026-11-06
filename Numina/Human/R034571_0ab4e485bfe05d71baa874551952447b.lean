import Mathlib

open Finset

theorem inequalities_132519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ∧
    (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ≤
    a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) := by
  wlog cleb : c ≤ b
  · specialize this a c b ha hc hb (by linarith only [cleb])
    rcases this with ⟨h1, h2⟩; constructor
    · calc
        _ = a + c + b := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = (a ^ 2 + c ^ 2) / (2 * b) + (c ^ 2 + b ^ 2) / (2 * a) + (b ^ 2 + a ^ 2) / (2 * c) := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  wlog clea : c ≤ a
  · specialize this c b a hc hb ha (by linarith only [clea, cleb]) (by linarith only [clea])
    rcases this with ⟨h1, h2⟩; constructor
    · calc
        _ = c + b + a := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = (c ^ 2 + b ^ 2) / (2 * a) + (b ^ 2 + a ^ 2) / (2 * c) + (a ^ 2 + c ^ 2) / (2 * b) := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  wlog blea : b ≤ a
  · specialize this b a c hb ha hc (by linarith) (by linarith) (by linarith)
    rcases this with ⟨h1, h2⟩; constructor
    · calc
        _ = b + a + c := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = (b ^ 2 + a ^ 2) / (2 * c) + (a ^ 2 + c ^ 2) / (2 * b) + (c ^ 2 + b ^ 2) / (2 * a) := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  constructor
  · let f : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
    let g : Fin 3 → ℝ := ![-1 / a, -1 / b, -1 / c]
    have fgmv : Monovary f g := by
      rw [monovary_iff_exists_antitone]; use Fin.instLinearOrder
      simp [f, g]; split_ands; any_goals rw [neg_div, neg_div]
      all_goals gcongr
    have CSI := Monovary.sum_smul_sum_le_card_smul_sum fgmv
    simp [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by decide] at CSI
    simp [f, g] at CSI; field_simp; rw [le_div_iff₀, ← sub_nonneg]; ring_nf
    field_simp at CSI; rw [div_le_div_iff_of_pos_right, ← sub_nonneg] at CSI
    ring_nf at CSI; linarith only [CSI]; all_goals positivity
  let f : Fin 3 → ℝ := ![a ^ 3, b ^ 3, c ^ 3]
  let g : Fin 3 → ℝ := ![1 / (b * c), 1 / (c * a), 1 / (a * b)]
  have fgmv : Monovary f g := by
    rw [monovary_iff_exists_antitone]; use Fin.instLinearOrder
    simp [f, g]; split_ands; gcongr; gcongr
    all_goals rw [mul_comm]; gcongr
  have CSI := Monovary.sum_smul_sum_le_card_smul_sum fgmv
  simp [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by decide] at CSI
  simp [f, g] at CSI; rw [← mul_le_mul_left (show (0:ℝ)<2 by norm_num)]
  rw [mul_add, mul_add, mul_div, mul_div_mul_left]
  rw [mul_div, mul_div_mul_left, mul_div, mul_div_mul_left]
  have : 2 * (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b)) =
  2 * (a ^ 4 + b ^ 4 + c ^ 4) / (c * a * b) := by field_simp; ring
  rw [this]; field_simp; rw [div_le_div_iff_of_pos_right, ← sub_nonneg]; ring_nf
  field_simp at CSI; rw [div_le_div_iff_of_pos_right, ← sub_nonneg] at CSI
  ring_nf at CSI; rw [← mul_le_mul_left (show 0< a*b*c by positivity)]
  rw [mul_zero]; calc
    _ ≤ _ := CSI
    _ = _ := by ring
  all_goals positivity