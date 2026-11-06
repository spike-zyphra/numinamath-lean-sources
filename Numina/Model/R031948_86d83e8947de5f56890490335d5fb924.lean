import Mathlib

theorem algebra_277210 {a b c d a' b' c' d' : ℝ} 
  (hb : b ≠ 0) (hd : d ≠ 0) (hb' : b' ≠ 0) (hd' : d' ≠ 0)
  (hbb' : b + b' ≠ 0) (hdd' : d + d' ≠ 0)
  (h₀ : a / b = c / d) (h₁ : a' / b' = c' / d') :
    (a + a') / (b + b') = (c + c') / (d + d') ↔ a*d' + a'*d = b*c' + b'*c := by
  constructor
  · -- Assume (a + a') / (b + b') = (c + c') / (d + d'), prove a*d' + a'*d = b*c' + b'*c
    intro h
    have h2 : a * d = c * b := by
      field_simp [hb, hd] at h₀
      linarith 
    have h5 : a' * d' = c' * b' := by
      field_simp [hb', hd'] at h₁ 
      linarith 
    have eq3 : (a + a') * (d + d') = (c + c') * (b + b') := by
      have eq5 : (a + a') * (d + d') = (b + b') * (c + c') := by
        have h2' : a / b = c / d := h₀
        have h' : (a + a') / (b + b') = (c + c') / (d + d') := h
        field_simp [hb, hd, hb', hd', hbb', hdd'] at h' h2' ⊢
        nlinarith [sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hd, sq_pos_of_ne_zero hb', sq_pos_of_ne_zero hd', sq_pos_of_ne_zero hbb', sq_pos_of_ne_zero hdd']
      linarith [eq5]
    have eq2 : a*d' + a'*d = b*c' + b'*c := by
      linarith [h2, h5, eq3]
    linarith [eq2]
  · -- Assume a*d' + a'*d = b*c' + b'*c, prove (a + a') / (b + b') = (c + c') / (d + d')
    intro h3
    have h7 : a * d = c * b := by 
      field_simp [hb, hd] at h₀ 
      linarith 
    have h7' : a' * d' = c' * b' := by 
      field_simp [hb', hd'] at h₁ 
      linarith 
    have eq3' : (a + a') * (d + d') = (c + c') * (b + b') := by
      have h8 : a * d = c * b := h7
      have h9 : a' * d' = c' * b' := h7'
      nlinarith [sq_nonneg (a * d' - a' * d), sq_nonneg (b * c' - b' * c), sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hd, sq_pos_of_ne_zero hb', sq_pos_of_ne_zero hd', sq_nonneg (b + b'), sq_nonneg (d + d'), sq_pos_of_ne_zero hbb', sq_pos_of_ne_zero hdd']
    have h5 : (a + a') / (b + b') = (c + c') / (d + d') := by
      field_simp [hb, hd, hb', hd', hbb', hdd']
      linarith [eq3']
    exact h5