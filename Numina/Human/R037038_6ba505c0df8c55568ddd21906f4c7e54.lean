import Mathlib

open Real Set
open scoped BigOperators

/-
  The monotonic increasing interval of the function $y=\log_{2}(2x-x^{2})$ is \_\_\_\_\_\_.
-/
theorem algebra_9470 {f : ℝ → ℝ} (hf : f = λ x => logb 2 (2 * x - x ^ 2)) (a b : ℝ) (h : a < b) (hdomain : ∀ x ∈ Set.Ioo a b, 2 * x - x ^ 2 > 0) :
    MonotoneOn f (Set.Ioo a b) ↔ (Set.Ioo a b) ⊆ Set.Ioo 0 1 := by

  -- determine domain (0, 2)
  have solve (x : ℝ) : 2 * x - x ^ 2 > 0 ↔ 0 < x ∧ x < 2 := by
    have : 2 * x - x ^ 2 = x * (2 - x) := by ring
    rw [this]
    constructor
    · intro hx
      by_contra h
      push_neg at h
      by_cases h' : x > 0
      · apply h at h'
        have : 2 - x ≤ 0 := by exact tsub_nonpos.mpr h'
        have : ¬ x * (2 - x) > 0 := by push_neg; refine mul_nonpos_of_nonneg_of_nonpos ?ha this; linarith
        contradiction
      · push_neg at h'
        have : ¬ x * (2 - x) > 0 := by push_neg; refine mul_nonpos_of_nonpos_of_nonneg h' ?_; linarith
        contradiction
    · intro hx
      obtain ⟨h1, h2⟩ := hx
      apply mul_pos h1
      linarith

  -- (a,b) must in the domain
  have hab : Set.Ioo a b ⊆ Set.Ioo 0 2 := by
    intro x hx
    apply hdomain x at hx
    apply (solve x).mp at hx
    exact hx

  -- obtain a ≥ 0
  have ha : a ≥ 0 := by
    by_contra ha
    push_neg at ha
    by_cases hb : b > 0
    · have : 0 ∈ Set.Ioo a b := by
        simp
        constructor
        · exact ha
        · exact hb
      apply hab at this
      simp at this
    · have : (a + b) / 2 ∈ Set.Ioo a b := by
        simp
        constructor <;> linarith
      apply hab at this
      simp at this
      linarith

  -- obtain b ≤ 2
  have hb : b ≤ 2 := by
    by_contra hb
    push_neg at hb
    by_cases ha : a < 2
    · have : 2 ∈ Set.Ioo a b := by
        simp
        constructor <;> linarith
      apply hab at this
      simp at this
    · have : (a + b) / 2 ∈ Set.Ioo a b := by
        simp
        constructor <;> linarith
      apply hab at this
      simp at this
      linarith

  -- f is monotene on (0, 1)
  have : MonotoneOn f (Set.Ioo 0 1) := by
    intro x₁ hx₁ x₂ hx₂ hle
    simp at hx₁ hx₂
    obtain ⟨hx1, hx2⟩ := hx₁
    have h1 : x₁ - x₂ ≤ 0 := by exact tsub_nonpos.mpr hle
    have h3 : 2 - x₁ - x₂ ≥ 0 := by linarith
    have : 2 * x₁ - x₁ ^ 2 - (2 * x₂ - x₂ ^ 2) ≤ 0 := by
      calc
        2 * x₁ - x₁ ^ 2 - (2 * x₂ - x₂ ^ 2) = (x₁ - x₂) * (2 - x₁ - x₂) := by linarith
        _ ≤ 0 := by exact mul_nonpos_of_nonpos_of_nonneg h1 h3
    simp [hf]
    refine logb_le_logb_of_le ?hb ?h ?hxy
    · norm_num
    · calc
         2 * x₁ - x₁ ^ 2 = x₁ * (2 - x₁) := by linarith
         _ > x₁ * (2 - 1) := by rel [hx1, hx2]
         _ > 0 := by norm_num; exact hx1
    · exact tsub_nonpos.mp this

  constructor <;> intro h
  · -- prove (a, b) ⊆ (0, 1)
    intro x hx
    simp at hx ⊢
    constructor
    · -- prove 0 < x
      linarith
    · -- prove x < 1
      by_contra hge
      push_neg at hge
      have hx' : x ∈ Ioo a b := by
        simp
        exact hx
      have hle : x ≤ (x + b) / 2 := by linarith
      have hx'' : (x + b) / 2 ∈ Ioo a b := by
        simp
        constructor <;> linarith
      apply h hx' hx'' at hle
      simp [hf] at hle
      -- use (x + b) / 2 to construct a contradiciton
      have : 2 * x - x ^ 2 ≤ 2 * ((x + b) / 2) - ((x + b) / 2) ^ 2 := by
        apply (logb_le_logb ?_ ?_ ?_).mp hle
        · norm_num
        · exact hdomain x hx
        · apply (solve ((x + b) / 2)).mpr
          constructor <;> linarith
      have : ¬ 2 * x - x ^ 2 ≤ 2 * ((x + b) / 2) - ((x + b) / 2) ^ 2 := by
        push_neg
        have h1 := hx.right
        have h1 : b - x > 0 := by exact sub_pos.mpr h1
        have h2 : 4 - 3 * x - b < 0 := by
          calc
            4 - 3 * x - b < 4 - 3 * x - x := by rel [hx.right]
            _ = 4 * (1 - x) := by ring
            _ ≤ 4 * (1 - 1) := by rel [hge]
            _ = 0 := by simp
        have : (b - x) * (4 - 3 * x - b) < 0 := by exact mul_neg_of_pos_of_neg h1 h2
        have : 2 * ((x + b) / 2) - ((x + b) / 2) ^ 2 - (2 * x - x ^ 2) < 0 := by
          calc
            2 * ((x + b) / 2) - ((x + b) / 2) ^ 2 - (2 * x - x ^ 2) = (b - x) - (b - x) * (3 * x + b) / 4 := by
              ring
            _ = (b - x) * (4 - 3 * x - b) / 4 := by linarith
            _ < 0 / 4 := by linarith
            _ = 0 := by simp
        linarith
      contradiction
  · -- if (a, b) ⊆ (0,1), then f is monotone
    exact MonotoneOn.mono this h
