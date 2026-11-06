import Mathlib

open Real

theorem inequalities_597360 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ 1 / 2 * ∑ i, a i := by
  have ha' : ∀ i : Fin n, a i > 0 := by 
    intro i 
    exact ha i 
  have hb' : ∀ i : Fin n, b i > 0 := by 
    intro i 
    exact hb i 
  have hpos : ∑ i : Fin n, a i > 0 := by 
    apply Finset.sum_pos 
    · intro i _ 
      exact ha' i 
    · use ⟨0, by linarith⟩ 
      simp [ha']
      <;> try linarith
  have hx1 : ∑ i : Fin n, (a i + b i) = 2 * (∑ i : Fin n, a i) := by 
    calc 
      ∑ i : Fin n, (a i + b i) = ∑ i : Fin n, (a i) + ∑ i : Fin n, (b i) := by 
        simp [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (a i)) + (∑ i : Fin n, (a i)) := by 
        rw [hsum]
      _ = 2 * (∑ i : Fin n, (a i)) := by 
        ring 
  have h7 : ∑ i, ((a i)^2 / (a i + b i)) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    have h6 : a i > 0 := ha' i
    have h7 : b i > 0 := hb' i
    have h8 : a i + b i > 0 := by 
      nlinarith 
    positivity 
  have h212 : (∑ i : Fin n, a i) ^ 2 / (2 * (∑ i : Fin n, a i)) = (∑ i : Fin n, a i) / 2 := by 
    have h666 : ∑ i : Fin n, a i > 0 := hpos 
    have h8 : (∑ i : Fin n, a i) ^ 2 = (∑ i : Fin n, a i) ^ 2 := by 
      rfl 
    field_simp [h666]
    <;> ring_nf  
  have hx2 : ∑ i, ((a i)^2 / (a i + b i)) ≥ (∑ i : Fin n, a i) / 2 := by 
    have hx4 : (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, (a i + b i)) = (∑ i : Fin n, a i) / 2 := by
      have eq1 : ∑ i : Fin n, (a i + b i) = 2 * (∑ i : Fin n, a i) := by 
        linarith [hx1] 
      rw [eq1] 
      exact h212
    linarith [h7, hx4]
  linarith [hx2]