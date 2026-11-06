import Mathlib

theorem algebra_300027 {x y z u: ℝ} (ne1: y + z + u ≠ 0) (ne2: z + u + x ≠ 0) (ne3: u + x + y ≠ 0) (ne4: x + y + z ≠ 0) 
  (ne5: z + u ≠ 0) (ne6: u + x ≠ 0) (ne7: x + y ≠ 0) (ne8: y + z ≠ 0)
   (h1: x / (y + z + u) = y / (z + u + x)) (h2: y / (z + u + x) = z / (u + x + y)) 
    (h3: z / (u + x + y) = u / (x + y + z)): 
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = -4 ∨ 
    (x + y) / (z + u) + (y + z) / (u + x) + (z + u) / (x + y) + (u + x) / (y + z) = 4 := by
  have eq1 : x * (z + u + x) - y * (y + z + u) = 0 := by
    field_simp [ne1, ne2] at h1 
    linarith
  have eq2 : y * (u + x + y) - z * (z + u + x) = 0 := by 
    field_simp [ne2, ne3] at h2 
    linarith
  have eq3 : z * (x + y + z) - u * (u + x + y) = 0 := by
    field_simp [ne3, ne4] at h3 
    linarith
  -- Now from eq1, which is x*(z + u + x) - y*(y + z + u) = 0
  -- Expanding, we get xz + xu + x² - y² - yz - yu = 0
  -- Rearranged: x² - y² + xz - yz + xu - yu = 0
  -- This factors to: (x - y)(x + y + z + u) = 0
  have eq1a : (x - y) * (x + y + z + u) = 0 := by 
    ring_nf at eq1 ⊢
    linarith
  -- Similarly, eq2 can be factored to (y - z)(x + y + z + u) = 0
  have eq2a : (y - z) * (x + y + z + u) = 0 := by 
    ring_nf at eq2 ⊢
    linarith
  -- Similarly, eq3 can be factored to (z - u)(x + y + z + u) = 0
  have eq3a : (z - u) * (x + y + z + u) = 0 := by 
    ring_nf at eq3 ⊢
    linarith
  by_cases h : x + y + z + u = 0
  · -- $x + Y + z + u = 0$
    left
    have h10 : (x + y) / (z + u) = -1 := by 
      have h11 : x + y = - (z + u) := by linarith 
      rw [h11]
      field_simp [ne5]
    have h20 : (y + z) / (u + x) = -1 := by 
      have h22 : y + z = - (u + x) := by linarith 
      rw [h22]
      field_simp [ne6]
    have h30 : (z + u) / (x + y) = -1 := by 
      have h33 : z + u = - (x + y) := by linarith 
      rw [h33]
      field_simp [ne7]
    have h40 : (u + x) / (y + z) = -1 := by 
      have h44 : u + x = - (y + z) := by 
        linarith 
      rw [h44]
      field_simp [ne8]
    rw [h10, h20, h30, h40]
    norm_num
  · -- x + y + z + u ≠ 0 
    have hx : x = y := by 
      have h4 : (x - y) * (x + y + z + u) = 0 := eq1a
      cases' (mul_eq_zero.mp h4) with h44 h444
      · linarith 
      · -- exfalso 
        exfalso 
        have h_eq : x + y + z + u = 0 := h444
        contradiction 
    have hy : y = z := by 
      have h5 : (y - z) * (x + y + z + u) = 0 := eq2a
      cases' (mul_eq_zero.mp h5) with h55 h555
      · linarith 
      · -- exfalso 
        exfalso 
        have h_eq : x + y + z + u = 0 := h555
        contradiction 
    have hz : z = u := by 
      have h6 : (z - u) * (x + y + z + u) = 0 := eq3a
      cases' (mul_eq_zero.mp h6) with h66 h666
      · linarith 
      · -- exfalso 
        exfalso 
        have h_eq : x + y + z + u = 0 := h666
        contradiction 
    -- From the above, we have x = y = z = u
    -- So all terms equal to 1.
    right 
    have h7 : x + x ≠ 0 := by
      intro h8
      have h88 : x = 0 := by linarith 
      have h9 : y = 0 := by 
        linarith [hx, h88]
      have h99 : z = 0 := by 
        linarith [hy, h9]
      have h999 : u = 0 := by 
        linarith [hz, h99]
      have h9999 : y + z + u = 0 := by 
        linarith [h999, h99, h9]
      contradiction
    -- Now we can calculate each of the fractions.
    have eq4 : (x + y) / (z + u) = 1 := by
      rw [show y = x by linarith, show z = x by linarith, show u = x by linarith]
      field_simp [h7]
    have eq5 : (y + z) / (u + x) = 1 := by
      rw [show y = x by linarith, show z = x by linarith, show u = x by linarith]
      field_simp [h7]
    have eq6 : (z + u) / (x + y) = 1 := by
      rw [show z = x by linarith, show u = x by linarith, show y = x by linarith]
      field_simp [h7]
    have eq7 : (u + x) / (y + z) = 1 := by
      rw [show u = x by linarith, show x = x by linarith, show y = x by linarith, show z = x by linarith]
      field_simp [h7]
    rw [eq4, eq5, eq6, eq7]
    norm_num