import Mathlib

theorem algebra_200692 {f : Polynomial ℤ} (hf : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ f.eval x = 2 ∧ f.eval y = 2 ∧ f.eval z = 2) :
    ∀ x : ℤ, f.eval x ≠ 3 := by
  rcases hf with ⟨x, y, z, hxy, hyz, hzx, hfx, hfy, hfz⟩
  intro w
  by_contra h
  have h1 : (w - x) ∣ (f.eval w - f.eval x) := by
    apply Polynomial.sub_dvd_eval_sub
  have h2 : (w - y) ∣ (f.eval w - f.eval y) := by
    apply Polynomial.sub_dvd_eval_sub
  have h3 : (w - z) ∣ (f.eval w - f.eval z) := by
    apply Polynomial.sub_dvd_eval_sub
  rw [show f.eval w - f.eval x = 1 by linarith [hfx, h]] at h1
  rw [show f.eval w - f.eval y = 1 by linarith [hfy, h]] at h2
  rw [show f.eval w - f.eval z = 1 by linarith [hfz, h]] at h3
  have h4 : (w - x) ∣ 1 := h1
  have h5 : (w - y) ∣ 1 := h2
  have h6 : (w - z) ∣ 1 := h3
  have h7 : (w - x) = 1 ∨ (w - x) = -1 := by
    have h : (w - x) ∣ 1 := h4
    have h8 : (w - x) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h
    have h9 : (w - x) ≥ -1 := by
      have h10 : -(w - x) ∣ 1 := by 
        exact Int.neg_dvd.2 h
      have h11 : -(w - x) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h10
      omega
    interval_cases h12 : (w - x) <;> tauto
  have h8 : (w - y) = 1 ∨ (w - y) = -1 := by
    have h : (w - y) ∣ 1 := h5
    have h8 : (w - y) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h
    have h9 : (w - y) ≥ -1 := by
      have h10 : -(w - y) ∣ 1 := by 
        exact Int.neg_dvd.2 h
      have h11 : -(w - y) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h10
      omega
    interval_cases h12 : (w - y) <;> tauto
  have h9 : (w - z) = 1 ∨ (w - z) = -1 := by
    have h : (w - z) ∣ 1 := h6
    have h8 : (w - z) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h
    have h9 : (w - z) ≥ -1 := by
      have h10 : -(w - z) ∣ 1 := by 
        exact Int.neg_dvd.2 h
      have h11 : -(w - z) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h10
      omega
    interval_cases h12 : (w - z) <;> tauto
  omega