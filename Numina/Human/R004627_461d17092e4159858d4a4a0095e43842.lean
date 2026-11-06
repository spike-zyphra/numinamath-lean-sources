import Mathlib

theorem algebra_290898 (x y z : ℤ) : 
(x + y + z = 0)∧(x^3 + y^3 + z^3 = -18) 
↔ 
(x=1∧y=2∧z=-3) ∨ (x=1∧y=-3∧z=2) ∨ (x=2∧y=1∧z=-3) ∨ (x=2∧y=-3∧z=1) ∨ (x=-3∧y=1∧z=2) ∨ (x=-3∧y=2∧z=1) := by

  constructor

  --From left to right
  --Rewrite the equation and we get xyz = -6.
  intro ⟨hs,h⟩ 
  have eq : x^3+y^3+z^3 - 3 * x * y * z = 0 := by
    have : x^3+y^3+z^3 - 3 * x * y * z = (x+y+z)*(x^2+y^2+z^2-x*y-y*z-z*x) := by ring
    rw [this]
    rw [hs]
    ring
  rw [h] at eq
  have t : x*y*z = -6 := by nlinarith

  --Wlog we can assume that x < 0.
  wlog xneg : x < 0
  have xnneg : 0 ≤ x := by linarith
  have ynzn : y < 0 ∨ z < 0 := by
    by_contra yznneg
    push_neg at yznneg
    
    by_cases ypos : 0 < y
    have : 0 < x + y + z := by linarith
    linarith
    have ye0 : y = 0 := by linarith
    rw [ye0] at t
    norm_num at t

  rcases ynzn with yneg | zneg

  have : y = 1 ∧ x = 2 ∧ z = -3 ∨ y = 1 ∧ x = -3 ∧ z = 2 ∨ y = 2 ∧ x = 1 ∧ z = -3 ∨ y = 2 ∧ x = -3 ∧ z = 1 ∨ y = -3 ∧ x = 1 ∧ z = 2 ∨ y = -3 ∧ x = 2 ∧ z = 1 := by 
    apply this
    linarith
    linarith
    linarith
    linarith
    exact yneg
  rcases this with h | h | h | h | h | h
  right;right;left; tauto
  right;right;right;right;left;tauto
  left;tauto
  right;right;right;right;right;tauto
  right;left;tauto
  right;right;right;left;tauto

  have : z = 1 ∧ y = 2 ∧ x = -3 ∨ z = 1 ∧ y = -3 ∧ x = 2 ∨ z = 2 ∧ y = 1 ∧ x = -3 ∨ z = 2 ∧ y = -3 ∧ x = 1 ∨ z = -3 ∧ y = 1 ∧ x = 2 ∨ z = -3 ∧ y = 2 ∧ x = 1 := by
    apply this
    linarith
    linarith
    linarith
    linarith
    exact zneg
  rcases this with h | h | h | h | h | h
  right;right;right;right;right;tauto
  right;right;right;left;tauto
  right;right;right;right;left;tauto
  right;left;tauto
  right;right;left;tauto
  left;tauto

  --Then -x can only be 1, 2, 3, or 6.
  have yzpos : 0 < y*z := by nlinarith
  let xx : ℕ := (-x).toNat
  have xxpos : 0 < xx := by simp [xx]; exact xneg
  have t1: xx = -x := by refine Int.toNat_of_nonneg ?_; linarith
  have t2: xx ∣ 6 := by 
    use (y*z).toNat
    have : (y*z).toNat = y*z := by apply Int.toNat_of_nonneg; nlinarith
    zify
    rw [this]
    rw [t1]
    linarith
  have uxx : xx ≤ 6 := by apply Nat.le_of_dvd; norm_num; exact t2
  -- We check every case separately.
  by_cases xxe : xx=1
  have : x = -1 := by omega
  rw [this] at hs t
  simp_all
  have : y = 1-z := by linarith
  rw [this] at t
  ring_nf at t
  have : z^2 -z + 6 =0 := by linarith
  have : 0 < z^2 -z + 6 := by 
    qify
    nlinarith
  linarith
  by_cases xxe : xx=2
  have : x = -2 := by omega
  rw [this] at hs t
  simp_all
  have : y = 2 - z := by linarith
  rw [this] at t
  ring_nf at t
  have : z^2 - 2 * z + 3 = 0 := by omega
  have : 0 < z^2 - 2 * z + 3 := by nlinarith
  linarith
  by_cases xxe : xx=3
  have : x = -3 := by omega
  rw [this] at hs t
  simp_all
  have : y = 3-z := by linarith
  rw [this] at t
  ring_nf at t
  have : (z-1)*(z-2) = 0 := by nlinarith
  have : z-1 = 0 ∨ z-2 = 0 := by simpa using this
  rcases this with h | h
  right;
  have : z=1 := by linarith
  rw [this] at hs
  have : y=2 := by linarith
  tauto
  left
  have : z=2 := by linarith
  rw [this] at hs
  have : y=1 := by linarith
  tauto
  by_cases xxe : xx=4
  rw [xxe] at t2; norm_num at t2
  by_cases xxe : xx=5
  rw [xxe] at t2; norm_num at t2
  have xxe : xx = 6 := by omega
  exfalso; 
  have : x = -6 := by omega
  rw [this] at hs t
  have : y*z = 1 := by nlinarith
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  rcases this
  omega
  omega
  



  --From right to left. Just simple calculation.
  intro h
  rcases h with h | h | h | h | h | h
  
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
  obtain ⟨hx,hy,hz⟩ := h
  simp [hx,hy,hz]
