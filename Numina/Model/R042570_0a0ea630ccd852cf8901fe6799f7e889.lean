import Mathlib


lemma lemma_1 {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 2 + x * y + y ^ 2 = 0) :
    (x / (x + y)) ^ 3 = -1 := by 
  have h1 : (x + y) ^ 2 = x * y := by
    calc
      (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
      _ = (x ^ 2 + x * y + y ^ 2) + x * y := by ring
      _ = 0 + x * y := by rw [h]
      _ = x * y := by ring
  have h2 : x ^ 3 + (x + y) ^ 3 = 0 := by
    have eq1 : (x + y) ^ 3 = (x + y) * (x * y) := by
      calc
        (x + y) ^ 3 = (x + y) * (x + y) ^ 2 := by ring
        _ = (x + y) * (x * y) := by rw [h1]
    calc
      x ^ 3 + (x + y) ^ 3 = x ^ 3 + (x + y) * (x * y) := by rw [eq1]
      _ = x ^ 3 + (x ^ 2 * y + x * y ^ 2) := by
        ring_nf
      _ = x * (x ^ 2 + x * y + y ^ 2) := by
        ring_nf
      _ = x * 0 := by
        rw [h]
      _ = 0 := by
        simp
  have h3 : x + y ≠ 0 := by
    by_contra h_eq
    have h_eq1 : y = -x := by
      have h_eq2 : x + y = 0 := by
        simpa using h_eq
      calc
        y = (x + y) - x := by ring
        _ = 0 - x := by rw [h_eq2]
        _ = -x := by ring
    rw [show y = -x by exact h_eq1] at h
    have h_eq2 : x ^ 2 = 0 := by
      simp [pow_two] at h ⊢
      exact h
    have h_eq3 : x = 0 := by
      simp at h_eq2 ⊢
      exact h_eq2
    contradiction
  have h4 : (x / (x + y)) ^ 3 = (x ^ 3) / (x + y) ^ 3 := by
    field_simp [h3]
  have h5 : x ^ 3 = - (x + y) ^ 3 := by
    have h_eq1 : x ^ 3 + (x + y) ^ 3 = 0 := by
      exact h2
    have h_eq2 : x ^ 3 = - (x + y) ^ 3 := by
      calc
        x ^ 3 = (x ^ 3 + (x + y) ^ 3) - (x + y) ^ 3 := by ring
        _ = 0 - (x + y) ^ 3 := by rw [h_eq1]
        _ = - (x + y) ^ 3 := by ring
    exact h_eq2
  have h6 : (x ^ 3) / (x + y) ^ 3 = -1 := by
    have h8 : (x + y) ^ 3 ≠ 0 := by
      have h9 : x + y ≠ 0 := h3
      simp [pow_ne_zero 3 h9]
    have h7 : (x + y) ^ 3 = -x ^ 3 := by
      calc
        (x + y) ^ 3 = -x ^ 3 := by
          calc
            (x + y) ^ 3 = - (x ^ 3) := by 
              rw [show x ^ 3 = - (x + y) ^ 3 by exact h5]
              all_goals ring
            _ = -x ^ 3 := by ring
        _ = -x ^ 3 := by ring
    field_simp [h8]
    rw [h7]
    all_goals 
      ring_nf 
  rw [h4]
  exact h6


theorem algebra_196749 {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x^2 + x * y + y^2 = 0) :
    (x / (x + y)) ^ 1990 + (y / (x + y)) ^ 1990 = -1 := by
  have hx1 : x + y ≠ 0 := by
    by_contra h_eq
    have h_eq1 : y = -x := by
      have h_eq2 : x + y = 0 := by
        simpa using h_eq
      calc
        y = (x + y) - x := by ring
        _ = 0 - x := by rw [h_eq2]
        _ = -x := by ring
    rw [show y = -x by exact h_eq1] at h
    have h_eq2 : x ^ 2 = 0 := by
      simp [pow_two] at h ⊢
      exact h
    have h_eq3 : x = 0 := by
      simp at h_eq2 ⊢
      exact h_eq2
    contradiction

  have h1 : (x / (x + y)) ^ 3 = -1 := by
    apply lemma_1 hx hy h

  have h2 : (y / (x + y)) ^ 3 = -1 := by
    have h_eq : y ^ 2 + y * x + x ^ 2 = 0 := by 
      have h_eq1 : x ^ 2 + x * y + y ^ 2 = 0 := by
        exact h
      have h_eq2 : y ^ 2 + y * x + x ^ 2 = x ^ 2 + x * y + y ^ 2 := by 
        ring_nf
      rw [h_eq2]
      exact h_eq1
    have h3 : (y / (y + x)) ^ 3 = -1 := by 
      apply lemma_1 hy hx (by 
        simpa [show y ^ 2 + y * x + x ^ 2 = 0 by exact h_eq]
      )
    have h4 : y + x = x + y := by ring
    rw [h4] at h3
    exact h3

  have h3 : (x / (x + y)) ^ 1990 = - (x / (x + y)) := by
    calc
      (x / (x + y)) ^ 1990 = (x / (x + y)) ^ (3 * 663 + 1) := by
        norm_num
      _ = ((x / (x + y)) ^ 3) ^ 663 * (x / (x + y)) := by 
        ring_nf
      _ = (-1) ^ 663 * (x / (x + y)) := by 
        rw [h1]
      _ = - (x / (x + y)) := by 
        ring_nf

  have h4 : (y / (x + y)) ^ 1990 = - (y / (x + y)) := by
    calc
      (y / (x + y)) ^ 1990 = (y / (x + y)) ^ (3 * 663 + 1) := by
        norm_num
      _ = ((y / (x + y)) ^ 3) ^ 663 * (y / (x + y)) := by 
        ring_nf
      _ = (-1) ^ 663 * (y / (x + y)) := by 
        rw [h2]
      _ = - (y / (x + y)) := by 
        ring_nf

  calc
    (x / (x + y)) ^ 1990 + (y / (x + y)) ^ 1990 = - (x / (x + y)) + - (y / (x + y)) := by 
      rw [h3, h4]
    _ = - (x / (x + y) + y / (x + y)) := by ring
    _ = - ((x + y) / (x + y)) := by 
      field_simp [hx1]
    _ = -1 := by
      field_simp [hx1]