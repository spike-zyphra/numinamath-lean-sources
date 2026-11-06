import Mathlib

open Real

theorem inequalities_116620 {n : ℕ} (hn : 2 ≤ n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (S : ℝ)
    (hS : ∑ i, a i = S ∧ ∑ i, b i = S) :
    ∑ i, (a i)^2 / (a i + b i) ≥ S / 2 ∧
    ∑ i, (a i)^2 / (a i + b i) = ∑ i, (b i)^2 / (a i + b i) := by
  have hS₁ : ∑ i, a i = S := hS.1
  have hS₂ : ∑ i, b i = S := hS.2
  have h_pos1 : ∀ i, 0 < a i + b i := by
    intro i
    have ha_i : 0 < a i := ha i
    have hb_i : 0 < b i := hb i
    linarith
  have h1 : ∑ i, (a i)^2 / (a i + b i) ≥ S / 2 := by
    have h2 : ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by
      apply Finset.sq_sum_div_le_sum_sq_div
      intro i hi
      have ha_i_pos : 0 < a i := ha i
      have hb_i_pos : 0 < b i := hb i
      exact h_pos1 i
    have h6 : ∑ i, (a i + b i) = 2 * S := by
      calc
        ∑ i, (a i + b i) = ∑ i, a i + ∑ i, b i := by
          simp [Finset.sum_add_distrib]
          <;> norm_num
          all_goals try { nlinarith }
        _ = S + S := by
          rw [hS₁, hS₂]
        _ = 2 * S := by ring
    have h3 : (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) = S / 2 := by
      have h6' : ∑ i, (a i + b i) = 2 * S := by
        linarith [h6]
      have h7 : (∑ i, a i) = S := by
        linarith [hS₁]
      rw [h6', h7]
      have h_s_pos : 0 < S := by
        have h3 : 0 < ∑ j : Fin n, a j := by
          apply Finset.sum_pos
          intro j hj
          have : 0 < a j := ha j
          exact this
          use ⟨0, by linarith [show 2 ≤ n by linarith]⟩
          simp at *
          <;> try { tauto }
          <;> try { nlinarith }
          all_goals linarith
        have h4_eq : ∑ j : Fin n, a j = S := by
          linarith [hS₁]
        linarith [h4_eq]
      have h_s_ne_zero : S ≠ 0 := by linarith [h_s_pos]
      have h8 : 0 < 2 * S := by nlinarith
      have h9 : 2 * S ≠ 0 := by nlinarith
      field_simp [show 2 * S ≠ 0 by exact h9, show S ≠ 0 by exact h_s_ne_zero]
      <;> ring_nf
      all_goals try { 
        nlinarith 
      }
      all_goals try { 
        tauto 
      }
      all_goals try { 
        nlinarith 
      }
      all_goals try { 
        tauto 
      }
    linarith [h2, h3]
  have h_eq : ∑ i, (a i)^2 / (a i + b i) = ∑ i, (b i)^2 / (a i + b i) := by
    have h7 : ∑ i, ((a i)^2 / (a i + b i) - (b i)^2 / (a i + b i)) = 0 := by
      have h8 : ∑ i, ((a i)^2 / (a i + b i) - (b i)^2 / (a i + b i)) = ∑ i, (a i - b i) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          have h_pos1_i : 0 < a i + b i := h_pos1 i
          have h9 : (a i)^2 / (a i + b i) - (b i)^2 / (a i + b i) = (a i - b i) := by
            field_simp
            <;> nlinarith [sq_nonneg (a i - b i)]
          linarith [h9]
      rw [h8]
      have h8 : ∑ i, (a i - b i) = (∑ i, a i) - (∑ i, b i) := by
        simp [Finset.sum_sub_distrib]
        <;> norm_num
      rw [h8, hS₁, hS₂]
      all_goals norm_num
    have eq1 : ∑ i, ((a i)^2 / (a i + b i) - (b i)^2 / (a i + b i)) = (∑ i, (a i)^2 / (a i + b i)) - (∑ i, (b i)^2 / (a i + b i)) := by
      simp [Finset.sum_sub_distrib]
      <;> norm_num
    rw [eq1] at h7
    linarith
  constructor
  · exact h1
  · exact h_eq