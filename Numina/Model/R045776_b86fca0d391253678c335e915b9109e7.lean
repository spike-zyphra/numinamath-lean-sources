import Mathlib

theorem algebra_254036 :
  { (x, y) : ℝ × ℝ | ∃ (p q : ℝ), p ≠ 1 ∧ q ≠ 1 ∧
    x + y - 1 ≠ 0 ∧ x - y - 1 ≠ 0 ∧
    (x + y + 1) / (x + y - 1) = p ∧ (x - y + 1) / (x - y - 1) = q } =
  { (x, y) : ℝ × ℝ | ∃ (p q : ℝ), p ≠ 1 ∧ q ≠ 1 ∧
    x = (p * q - 1) / ((p - 1) * (q - 1)) ∧ y = (q - p) / ((p - 1) * (q - 1)) } := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Forward direction: prove that (x,y) satisfying the system is in the second set
    rintro ⟨p, q, hp, hq, h1, h2, he1, he2⟩
    have eq1 : x + y - 1 ≠ 0 := h1
    have eq2 : x - y - 1 ≠ 0 := h2
    have eq3 : (x + y + 1) / (x + y - 1) = p := he1
    have eq4 : (x - y + 1) / (x - y - 1) = q := he2
    have eq5 : x + y = (p + 1) / (p - 1) := by
      have hne : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have eq9 : x + y + 1 = p * (x + y - 1) := by 
        field_simp [show x + y - 1 ≠ 0 by exact h1] at eq3 ⊢ 
        all_goals linarith
      have eq10 : (x + y) * (1 - p) = - (p + 1) := by 
        linarith [eq9]
      have eq11 : x + y = (p + 1) / (p - 1) := by
        have hne : p - 1 ≠ 0 := by
          intro h
          apply hp
          linarith
        field_simp [hne]
        linarith [eq10]
      linarith
    have eq12 : x - y = (q + 1) / (q - 1) := by
      have hne : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      have eq14 : x - y + 1 = q * (x - y - 1) := by 
        field_simp [show x - y - 1 ≠ 0 by exact h2] at eq4 ⊢ 
        all_goals linarith
      have eq15 : (x - y) * (1 - q) = - (q + 1) := by 
        linarith [eq14]
      have eq16 : x - y = (q + 1) / (q - 1) := by
        have hne : q - 1 ≠ 0 := by
          intro h
          apply hq
          linarith
        field_simp [hne]
        linarith [eq15]
      linarith
    have h3 : x = (p * q - 1) / ((p - 1) * (q - 1)) := by
      have eq17 : x = ( (p + 1) / (p - 1) + (q + 1) / (q - 1) ) / 2 := by
        have h4 : x + y = (p + 1) / (p - 1) := eq5
        have h5 : x - y = (q + 1) / (q - 1) := eq12
        linarith
      have hne1 : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have hne2 : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      rw [eq17]
      field_simp [(show p - 1 ≠ 0 by assumption), (show q - 1 ≠ 0 by assumption)]
      ring
    have h4 : y = (q - p) / ((p - 1) * (q - 1)) := by
      have eq19 : y = ( (p + 1) / (p - 1) - (q + 1) / (q - 1) ) / 2 := by
        have h4 : x + y = (p + 1) / (p - 1) := eq5
        have h5 : x - y = (q + 1) / (q - 1) := eq12
        linarith
      have hne1 : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have hne2 : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      rw [eq19]
      field_simp [(show p - 1 ≠ 0 by assumption), (show q - 1 ≠ 0 by assumption)]
      ring
    refine' ⟨p, q, hp, hq, h3, h4⟩
  · -- Backward direction: prove that (x,y) in the second set satisfies the system
    rintro ⟨p, q, hp, hq, hx, hy⟩
    have h3 : x = (p * q - 1) / ((p - 1) * (q - 1)) := by linarith
    have h4 : y = (q - p) / ((p - 1) * (q - 1)) := by linarith
    have h5 : x + y = (p + 1) / (p - 1) := by
      rw [h3, h4]
      have hne1 : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have hne2 : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      field_simp [(show p - 1 ≠ 0 by assumption), (show q - 1 ≠ 0 by assumption)]
      ring
    have h6 : x - y = (q + 1) / (q - 1) := by
      rw [h3, h4]
      have hne1 : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have hne2 : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      field_simp [(show p - 1 ≠ 0 by assumption), (show q - 1 ≠ 0 by assumption)]
      ring
    have h1 : x + y - 1 ≠ 0 := by
      by_contra h
      have h7 : x + y = 1 := by linarith
      rw [h7] at h5
      have hne1 : p - 1 ≠ 0 := by
        intro h
        apply hp
        linarith
      have heq : (p + 1) / (p - 1) = 1 := by
        linarith
      have heq2 : p + 1 = p - 1 := by
        have hne1 : p - 1 ≠ 0 := by
          intro h
          apply hp
          linarith
        field_simp [hne1] at heq ⊢
        all_goals linarith
      nlinarith
    have h2 : x - y - 1 ≠ 0 := by
      by_contra h
      have h7 : x - y = 1 := by linarith
      rw [h7] at h6
      have hne2 : q - 1 ≠ 0 := by
        intro h
        apply hq
        linarith
      have heq : (q + 1) / (q - 1) = 1 := by
        linarith
      have heq2 : q + 1 = q - 1 := by
        have hne2 : q - 1 ≠ 0 := by
          intro h
          apply hq
          linarith
        field_simp [hne2] at heq ⊢
        all_goals linarith
      nlinarith
    refine' ⟨p, q, hp, hq, h1, h2, ?_, ?_⟩
    · -- Show (x + y + 1) / (x + y - 1) = p
      have hne1 : x + y - 1 ≠ 0 := h1
      have heq : (x + y + 1) / (x + y - 1) = p := by
        have h7 : x + y = (p + 1) / (p - 1) := h5
        have eq1 : x + y + 1 = (2 * p) / (p - 1) := by
          rw [h7]
          have hne1 : p - 1 ≠ 0 := by
            intro h
            apply hp
            linarith
          field_simp [hne1]
          ring
        have eq2 : x + y - 1 = 2 / (p - 1) := by
          rw [h7]
          have hne1 : p - 1 ≠ 0 := by
            intro h
            apply hp
            linarith
          field_simp [hne1]
          ring
        rw [eq1, eq2]
        have hne1 : p - 1 ≠ 0 := by
          intro h
          apply hp
          linarith
        field_simp [hne1]
        all_goals ring
      linarith
    · -- Show (x - y + 1) / (x - y - 1) = q
      have hne2 : x - y - 1 ≠ 0 := h2
      have heq : (x - y + 1) / (x - y - 1) = q := by
        have h7 : x - y = (q + 1) / (q - 1) := h6
        have eq1 : x - y + 1 = (2 * q) / (q - 1) := by
          rw [h7]
          have hne2 : q - 1 ≠ 0 := by
            intro h
            apply hq
            linarith
          field_simp [hne2]
          ring
        have eq2 : x - y - 1 = 2 / (q - 1) := by
          rw [h7]
          have hne2 : q - 1 ≠ 0 := by
            intro h
            apply hq
            linarith
          field_simp [hne2]
          ring
        rw [eq1, eq2]
        have hne2 : q - 1 ≠ 0 := by
          intro h
          apply hq
          linarith
        field_simp [hne2]
        all_goals ring
      linarith