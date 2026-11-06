import Mathlib

theorem algebra_116100 {x : ℂ} (hx : x ≠ 0) (h : x + 1 / x = 1) :
    x^2014 + 1 / x^2014 = -1 := by
  have h1 : x ^ 2 + 1 = x := by
    have eq1 : x + 1 / x = 1 := h
    have eq2 : x ^ 2 + 1 = x := by
      calc
        x ^ 2 + 1 = x * (x + 1 / x) := by 
          field_simp [hx]
          <;> ring_nf
          <;> field_simp [hx]
          <;> ring_nf
        _ = x * 1 := by 
          rw [eq1]
        _ = x := by 
          ring
    exact eq2
  have h3 : x ^ 3 = -1 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (x - 1) := by 
        have h1' : x ^ 2 = x - 1 := by
          have eq1 : x ^ 2 + 1 = x := h1
          calc
            x ^ 2 = x ^ 2 + 1 - 1 := by ring
            _ = x - 1 := by 
              rw [eq1]
              all_goals ring_nf 
              <;> simp [Complex.ext_iff]
              <;> ring_nf
        rw [h1']
      _ = x ^ 2 - x := by ring
      _ = (x - 1) - x := by
        have h1' : x ^ 2 = x - 1 := by
          have eq1 : x ^ 2 + 1 = x := h1
          calc
            x ^ 2 = x ^ 2 + 1 - 1 := by ring
            _ = x - 1 := by 
              rw [eq1]
              all_goals ring_nf 
              <;> simp [Complex.ext_iff]
              <;> ring_nf
        rw [h1']
      _ = -1 := by
        have h' : x + 1 / x = 1 := h
        field_simp [hx] at h' ⊢
        <;> ring_nf at h' ⊢
        <;> norm_num [Complex.ext_iff] at h' ⊢
        all_goals 
          try { 
            simp [Complex.ext_iff] at h' ⊢
            <;> ring_nf at h' ⊢
            <;> norm_num at h' ⊢
          }
        all_goals try tauto
        all_goals try { exact_mod_cast h }
        all_goals try { 
          have eq2 : x.re^2 + x.im^2 > 0 := by 
            have ne : x ≠ 0 := hx
            simp [Complex.ext_iff, ne]
            all_goals nlinarith [sq_pos_of_pos (show (0:ℝ) < 1 by norm_num)]
          nlinarith [sq_nonneg (x.re), sq_nonneg (x.im)]
        }
        all_goals try { 
          have o1 : (x.re) = (x.re) := rfl
          nlinarith [sq_nonneg (x.re), sq_nonneg (x.im)]
        }
  have h6 : x ^ 6 = 1 := by
    calc 
      x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h3]
      _ = 1 := by norm_num
  have eq2 : x ^ 2014 = x ^ 4 := by
    calc 
      x ^ 2014 = x ^ (6 * 335 + 4) := by norm_num
      _ = (x ^ 6) ^ 335 * x ^ 4 := by ring_nf
      _ = (1) ^ 335 * x ^ 4 := by rw [h6]
      _ = x ^ 4 := by ring_nf
  have h4 : x ^ 4 = -x := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = x * (-1) := by rw [h3]
      _ = -x := by ring
  have h5 : 1 / x ^ 4 = -1 / x := by
    rw [show x ^ 4 = -x by exact h4]
    field_simp [hx]
    <;> ring_nf <;> norm_num
  calc
    x ^ 2014 + 1 / x ^ 2014 = x ^ 4 + 1 / x ^ 4 := by 
      rw [eq2]
    _ = x ^ 4 + (-1 / x) := by 
      rw [h5]
    _ = -x + (-1 / x) := by 
      rw [h4]
    _ = - (x + 1 / x ) := by 
      ring_nf
    _ = -1 := by 
      rw [h]