import Mathlib

open Real

theorem inequalities_303973 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∑ i : Fin n, a i = 1) (hb : ∑ i : Fin n, b i = 1)
    (ha' : ∀ i : Fin n, 0 < a i) (hb' : ∀ i : Fin n, 0 < b i) :
    ∑ i : Fin n, (a i)^2 / (a i + b i) ≥ 1 / 2 := by
  have h1 : ∀ i ∈ Finset.univ, 0 < a i + b i := by
    intro i hi
    have ha_i := ha' i
    have hb_i := hb' i
    linarith
  have h2 : ∑ i : Fin n, (a i)^2 / (a i + b i) ≥ (∑ i : Fin n, a i)^2 / (∑ i : Fin n, (a i + b i)) := by
    apply Finset.sq_sum_div_le_sum_sq_div
    intro i hi
    exact h1 i hi
  have ha2 : (∑ i : Fin n, a i) = 1 := ha
  have hsum : (∑ i : Fin n, (a i + b i)) = 2 := by
    calc (∑ i : Fin n, (a i + b i))
        = (∑ i : Fin n, a i) + (∑ i : Fin n, b i) := by simp [Finset.sum_add_distrib]
        _ = (∑ i : Fin n, a i) + 1 := by rw [hb]
        _ = 1 + 1 := by rw [ha]
        _ = 2 := by norm_num
  have h3 : (∑ i : Fin n, a i)^2 / (∑ i : Fin n, (a i + b i)) = 1 / 2 := by 
    rw [ha2, hsum]
    all_goals norm_num
  linarith [h2, h3]