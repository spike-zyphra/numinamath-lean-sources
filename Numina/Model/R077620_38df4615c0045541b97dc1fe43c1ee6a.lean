import Mathlib

theorem algebra_161825 (v_t v_e l_t l_e : ℝ)
    (h_v : v_t = 2 * v_e) (h_l : l_t = 3 * l_e)
    (h_t : l_t / v_t = 5) :
    (l_t + l_e) / (v_t + v_e) = 40 / 9 := by
  have h1 : v_t ≠ 0 := by
    by_contra h
    rw [h] at h_t
    norm_num at h_t
  have h2 : l_t = 5 * v_t := by
    field_simp [h1] at h_t
    linarith
  have h3 : l_t = 10 * v_e := by 
    rw [show v_t = 2 * v_e by linarith [h_v]] at h2
    linarith
  have h4 : 3 * l_e = 10 * v_e := by 
    rw [show l_t = 3 * l_e by linarith [h_l]] at h3 
    linarith
  have h5 : l_e = (10 / 3) * v_e := by 
    linarith
  have h7 : l_t + l_e = (40 / 3) * v_e := by 
    linarith [h3, h5]
  have h8 : v_t + v_e = 3 * v_e := by 
    linarith [h_v]
  have h9 : v_e ≠ 0 := by 
    by_contra h
    have : v_t = 0 := by linarith [h_v, h]
    contradiction
  rw [h7, h8]
  <;> try { 
    have h10 : v_e ≠ 0 := h9 
    field_simp [h10]
    <;> try ring_nf
    <;> try { 
      nlinarith [h9]
    }
  }
  <;> try { 
    nlinarith [h9]
  }
  all_goals try { 
    linarith
  }
  <;> try { 
    linarith
    <;> try { 
      nlinarith [h9]
    }
  }
  all_goals try { 
    nlinarith [h9]
    <;> try { 
      field_simp [h9]
    }
  }
  all_goals try { 
    field_simp [h9]
    <;> try ring_nf
  }
  all_goals try { 
    nlinarith [h9]
  }