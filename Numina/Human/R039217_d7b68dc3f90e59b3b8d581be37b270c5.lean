import Mathlib

theorem algebra_302380 : {(a, b, c) : ℤ × ℤ × ℤ | a < b ∧ b < c ∧ a * b + b * c + c * a = a * b * c ∧ a ≥ 1} = {(2, 3, 6)} := by 
  ext x
  constructor
  · -- one inclusion
    intro h
    simp at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    let a := x.1
    let b := x.2.1
    let c := x.2.2
    have ineq1 : a * b * c < 3 * b * c := by nlinarith
    have alt : a < 3 := by 
      by_contra! hc
      have : a * b * c ≥ 3 * b * c := by 
        apply mul_le_mul _ (by linarith)
        nlinarith
        nlinarith
        apply mul_le_mul hc (by linarith)
        nlinarith
        nlinarith
      nlinarith
    simp
    have age : a ≥ 1 := by linarith
    have aeqx1 : a = x.1 := by simp
    -- since a < 3, discuss case by case
    have x1le : x.1 < 3 := by omega
    interval_cases x.1
    -- the case a = 1
    · simp at h3
      have baddc : b + c= 0 := by nlinarith
      have : b = 0 ∧ c = 0 := by omega
      nlinarith
    -- the case a = 2
    · have eq_aux : b * c - 2 * b - 2 * c = 0:= by 
        unfold b
        unfold c
        calc 
          _ = 2 * x.2.1 * x.2.2 - 2 * x.2.1 - 2 * x.2.2 - x.2.1 * x.2.2 := by
            ring
          _ = _ := by 
            rw [←h3]; ring
      have eq_aux1 : (b - 2) * (c - 2) = 4 := by nlinarith
      have ineq3 : b - 2 < c -2 := by nlinarith
      have dvd_aux : b - 2 ∣ 4 := by exact Dvd.intro (c-2) eq_aux1
      have div_set : b - 2 = 1 ∨ b - 2 = 2 ∨ b - 2 = 4 := by
        have ble :b - 2 ≤ 4 := by 
          apply Int.le_of_dvd
          positivity
          exact dvd_aux
        have bge3 : b ≥ 3 := by nlinarith
        have bge : b - 2 ≥ 1 := by nlinarith
        interval_cases (b - 2)
        left;rfl
        right; left; rfl
        norm_num at dvd_aux
        right; right; rfl
      obtain hb1 | hb2 | hb3 := div_set
      · have ht1 : b = 3 := by omega
        rw [ht1] at eq_aux1
        have ht2 : c = 6 := by omega
        have aeq : a = 2 := by 
          rw [aeqx1]
        rw [←ht1, ←ht2, ←aeq]
      · 
        have ht2 : b = 4 := by omega
        have : c = 3 := by nlinarith
        unfold c at this
        rw [this] at h2
        unfold b at ht2
        rw [ht2] at h2
        simp at h2
      · 
        have ht3 : b = 6 := by omega
        rw [ht3] at eq_aux1
        norm_num at eq_aux1
        have ceq : c = 3 := by nlinarith
        unfold c at ceq
        rw [ceq] at h2
        unfold b at ht3
        rw [ht3] at h2
        simp at h2
  · -- the other inclusion
    intro h
    simp_all