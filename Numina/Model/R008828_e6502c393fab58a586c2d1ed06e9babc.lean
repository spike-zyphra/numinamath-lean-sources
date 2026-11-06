import Mathlib

theorem algebra_21230 {BrightVolume FreshVolume GlowVolume BrightCost FreshCost GlowCost : ℝ} (hpos : BrightVolume > 0 ∧ FreshVolume > 0 ∧ GlowVolume > 0 ∧ BrightCost > 0 ∧ FreshCost > 0 ∧ GlowCost > 0)
    (h1 : BrightCost = (1 + 60 / 100) * FreshCost) (h2 : BrightVolume = (1 - 25 / 100) * GlowVolume) (h3 : GlowCost = (1 - 25 / 100) * BrightCost) (h4 : GlowVolume = (1 + (33 + 1 / 3) / 100) * FreshVolume) (h5 : FreshCost / FreshVolume = 1) :
    (GlowCost / GlowVolume) * 100 = 90 := by
  rcases hpos with ⟨hB1, hF1, hG1, hB2, hF2, hG2⟩
  have h6 : FreshCost = FreshVolume := by
    have hp : FreshVolume > 0 := hF1
    field_simp at h5
    nlinarith
  have h7 : BrightCost = (1 + 60 / 100 : ℝ) * FreshCost := h1
  have h8 : BrightCost = 1.6 * FreshVolume := by
    rw [h7]
    rw [show FreshCost = FreshVolume by linarith [h6]]
    all_goals ring_nf
    <;> nlinarith
    all_goals ring_nf
    all_goals nlinarith
  have h9 : GlowCost = 1.2 * FreshVolume := by
    have h10 : GlowCost = (1 - 25 / 100 : ℝ) * BrightCost := h3
    rw [h10]
    rw [show BrightCost = 1.6 * FreshVolume by linarith [h8]]
    ring_nf
    <;> nlinarith
    all_goals ring_nf
    all_goals nlinarith
  have h10 : GlowVolume = (4 / 3 : ℝ) * FreshVolume := by
    have h11 : GlowVolume = (1 + (33 + (1/3)) / 100 : ℝ) * FreshVolume := h4
    rw [h11]
    ring_nf
    <;> field_simp
    <;> ring_nf <;> nlinarith
    <;> ring_nf
    <;> nlinarith
  have h11 : (GlowCost / GlowVolume) * 100 = 90 := by
    rw [show GlowCost = 1.2 * FreshVolume by linarith [h9]]
    rw [show GlowVolume = (4 / 3 : ℝ) * FreshVolume by linarith [h10]]
    have hp : FreshVolume > 0 := hF1
    field_simp
    <;> ring_nf
    <;> nlinarith
  linarith [h11]