import Mathlib

theorem algebra_177219 {x y : ℕ} (hxy : x > 0 ∧ y > 0) (hxy1 : x = y + 10) (h : (x * y - 40) / x = 39 ∧ (x * y - 40) % x = 22) :
    x = 3141 := by
  have eq1 : x = y + 10 := hxy1
  rcases h with ⟨hc1, hc2⟩
  have eq2 : x > 0 := hxy.1
  have eq3 : y > 0 := hxy.2
  have h1 : x * y ≥ 40 := by
    by_contra h2
    push_neg at h2
    have eq4 : x * y < 40 := h2
    have eq7 : x * y - 40 = 0 := by
      omega
    have eq8 : (x * y - 40) % x = 0 := by
      rw [eq7]
      simp
    omega
  have h2 : x * y - 40 = x * 39 + 22 := by
    have h3 : x * y - 40 = x * ((x * y - 40) / x) + ( (x * y - 40) % x ) := by
      have h4 : x * ((x * y - 40) / x) + ((x * y - 40) % x) = x * y - 40 := by
        have h5 : x * y - 40 = x * ((x * y - 40) / x) + ( (x * y - 40) % x ) := by
          rw [Nat.div_add_mod (x * y - 40) x]
        linarith
      linarith
    rw [hc1, hc2] at h3
    omega
  have h3 : x * y = x * 39 + 62 := by 
    omega
  rw [eq1] at h3
  have eq7 : (y + 10) * y = (y + 10) * 39 + 62 := by 
    linarith [h3]
  have hy1 : y ≤ 40 := by 
    nlinarith
  interval_cases y <;> omega