import Mathlib

open Real Finset

theorem inequalities_312234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) :
    3 * a * b * c ≤ a * b + b * c + a * c ∧ a * b + b * c + a * c ≤ a * b * c + 2 := by
  wlog aleb : a ≤ b
  · specialize this b a c hb ha hc (by rw [← h]; ring) (by linarith only [aleb])
    rcases this with ⟨h1, h2⟩; constructor
    · calc
        _ = 3 * b * a * c := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = b * a + a * c + b * c := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  wlog alec : a ≤ c
  · specialize this c b a hc hb ha (by rw [← h]; ring) (by linarith only [alec, aleb])
    specialize this (by linarith only [alec]); rcases this with ⟨h1, h2⟩
    constructor
    · calc
        _ = 3 * c * b * a := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = c * b + b * a + c * a := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  wlog blec : b ≤ c
  · specialize this a c b ha hc hb (by rw [← h]; ring) alec aleb (by linarith only [blec])
    rcases this with ⟨h1, h2⟩; constructor
    · calc
        _ = 3 * a * c * b := by ring
        _ ≤ _ := h1
        _ = _ := by ring
    calc
      _ = a * c + c * b + a * b := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  let w1 : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]
  let z1 : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
  have aux1 : ∀ i ∈ Finset.univ, 0 ≤ w1 i := by
    simp [w1]; intro i; fin_cases i
    all_goals simp
  have aux2 : 0 < ∑ i ∈ Finset.univ, w1 i := by
    simp [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by decide, w1]
    norm_num
  have aux3 : ∀ i ∈ Finset.univ, 0 ≤ z1 i := by
    simp [z1]; intro i; fin_cases i
    all_goals simp; positivity
  have AMGM1 := geom_mean_le_arith_mean Finset.univ w1 z1 aux1 aux2 aux3
  simp [sum_fin_eq_sum_range, prod_fin_eq_prod_range] at AMGM1
  simp [show range 3 = {0, 1, 2} by decide, w1, z1] at AMGM1
  rw [← mul_rpow, ← mul_rpow, ← mul_pow, ← mul_pow] at AMGM1
  norm_num at AMGM1; rw [← rpow_natCast] at AMGM1
  push_cast at AMGM1; rw [← rpow_mul] at AMGM1
  rw [← mul_add, ← mul_add, ← add_assoc, ← mul_assoc] at AMGM1
  norm_num at AMGM1; rw [one_div_mul_eq_div] at AMGM1
  rw [le_div_iff₀, ← add_le_add_iff_right (a * b * c)] at AMGM1
  rw [h] at AMGM1; clear aux1 aux2 aux3 w1 z1
  let f : ℝ → ℝ := fun x => x ^ ((2 : ℝ) / 3) * 3 + x
  have fmono : StrictMonoOn f (Set.Ioi 0) := by
    intro x; simp; intro hx y hy xlty
    dsimp [f]; gcongr
  replace AMGM1 : f (a * b * c) ≤ f 1 := by
    simp [f]; norm_num; exact AMGM1
  rw [fmono.le_iff_le] at AMGM1
  constructor
  · have : (a * b) ^ ((1 : ℝ) / 3) * (b * c) ^ ((1 : ℝ) / 3) * (a * c) ^ ((1 : ℝ) / 3)
    ≤ 1 / 3 * (a * b) + 1 / 3 * (b * c) + 1 / 3 * (a * c) := by
      apply geom_mean_le_arith_mean3_weighted
      any_goals positivity
      norm_num
    rw [← mul_rpow, ← mul_rpow, ← mul_add, ← mul_add] at this
    rw [one_div_mul_eq_div, le_div_iff₀'] at this
    rw [show a * b * (b * c) * (a * c) = (a * b * c) ^ 2 by ring] at this
    rw [← rpow_natCast] at this; push_cast at this
    rw [← rpow_mul] at this; norm_num at this
    apply le_trans _ this; calc
      _ = 3 * (a * b * c) := by ring
      _ ≤ _ := by
        rw [mul_le_mul_left, ← pow_le_pow_iff_left₀ _ _ (show 3≠0 by simp)]
        nth_rw 2 [← rpow_natCast]; push_cast
        rw [← rpow_mul]; norm_num
        rw [pow_succ]; nth_rw 2 [← mul_one ((a * b * c) ^ 2)]
        gcongr; all_goals positivity
    all_goals positivity
  rcases le_or_lt 1 b with h'|h'
  · have : 0 ≤ a * (b - 1) * (c - 1) := by
      rw [mul_assoc]; apply mul_nonneg; positivity
      apply mul_nonneg; linarith only [h']
      linarith only [h', blec]
    rw [show a*(b-1)*(c-1) = a*b*c+a-(a*b+a*c) by ring] at this
    rw [sub_nonneg, ← add_le_add_iff_right (b * c)] at this
    calc
      _ = a * b + a * c + b * c := by ring
      _ ≤ _ := this
      _ ≤ _ := by
        rw [add_assoc, add_le_add_iff_left, ← le_sub_iff_add_le']
        rw [← mul_le_mul_left (show 0<2+a by positivity), ← sq_sub_sq]
        norm_num; rw [← h, ← sub_nonneg]; ring_nf
        rw [show -(b * c * 2) + b ^ 2 + c ^ 2 = (b - c) ^ 2 by ring]
        apply sq_nonneg
  have : 0 ≤ (a - 1) * (b - 1) * c := by
    apply mul_nonneg; apply mul_nonneg_of_nonpos_of_nonpos
    linarith only [aleb, h']; linarith only [h']
    positivity
  rw [show (a-1)*(b-1)*c = a*b*c+c-(a*c+b*c) by ring] at this
  rw [sub_nonneg, ← add_le_add_iff_right (a * b)] at this
  calc
    _ = a * c + b * c + a * b := by ring
    _ ≤ _ := this
    _ ≤ _ := by
      rw [add_assoc, add_le_add_iff_left, ← le_sub_iff_add_le']
      rw [← mul_le_mul_left (show 0<2+c by positivity), ← sq_sub_sq]
      norm_num; rw [← h, ← sub_nonneg]; ring_nf
      rw [show -(a * b * 2) + a ^ 2 + b ^ 2 = (a - b) ^ 2 by ring]
      apply sq_nonneg
  any_goals simp
  all_goals positivity