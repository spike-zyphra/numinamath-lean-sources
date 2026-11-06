import Mathlib

theorem algebra_94057 (f : ℝ → ℝ) (hf : ∀ x y, |f x - f y| ≤ 1 / 2 * |x - y|)
    (h300 : f 300 = f 900) :
    f (f 800) - f (f 400) ≤ 50 := by 
  have h1 := hf 800 900
  have h2 := hf 400 300
  have h3 := hf 800 400
  have h4 := hf (f 800) (f 400)
  have h5 := hf 800 800
  have h6 := hf 400 400
  have h7 : |f 800 - f 900| ≤ 1 / 2 * |(800 : ℝ) - 900| := by
    simpa using h1
  have h8 : |f 400 - f 300| ≤ 1 / 2 * |(400 : ℝ) - 300| := by
    simpa using h2
  have h9 : |f 800 - f 400| ≤ 1 / 2 * |(800 : ℝ) - 400| := by
    simpa using h3
  have h10 : |f (f 800) - f (f 400)| ≤ 1 / 2 * |f 800 - f 400| := by
    simpa using h4
  have h800_900 : |f 800 - f 900| ≤ 50 := by
    norm_num at h7 ⊢
    linarith [h7]
  have h400_300 : |f 400 - f 300| ≤ 50 := by
    norm_num at h8 ⊢
    linarith [h8]
  have h400_900 : |f 400 - f 900| ≤ 50 := by
    have h10' : f 300 = f 900 := h300
    have h11 : f 400 - f 300 = f 400 - f 900 := by
      rw [h10']
    have h12 : |f 400 - f 300| = |f 400 - f 900| := by
      rw [h11]
    linarith [h12, h400_300]
  have h800_400' : |f 800 - f 400| ≤ 100 := by
    have h1 : |f 800 - f 900| ≤ 50 := by
      linarith [h800_900]
    have h2 : |f 400 - f 900| ≤ 50 := by
      linarith [h400_900]
    have h3 : |f 800 - f 400| ≤ |f 800 - f 900| + |f 900 - f 400| := by
      have h4 : f 800 - f 400 = (f 800 - f 900) + (f 900 - f 400) := by ring
      rw [h4]
      apply abs_add
    have h5 : |f 900 - f 400| = |f 400 - f 900| := by
      rw [show f 900 - f 400 = -(f 400 - f 900) by ring]
      rw [abs_neg]
    have h6 : |f 900 - f 400| ≤ 50 := by
      linarith [h5, h2]
    linarith [h1, h6, h3]
  have h11 : |f (f 800) - f (f 400)| ≤ 50 := by
    have h12 : |f (f 800) - f (f 400)| ≤ 1 / 2 * |f 800 - f 400| := by
      simpa using h4
    have h13 : |f 800 - f 400| ≤ 100 := by
      linarith [h800_400']
    nlinarith [abs_nonneg (f (f 800) - f (f 400)), abs_nonneg (f 800 - f 400), h12, h13]
  cases' abs_le.mp h11 with h14 h15
  linarith [h14]