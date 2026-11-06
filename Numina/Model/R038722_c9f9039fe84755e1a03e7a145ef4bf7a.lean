import Mathlib


theorem algebra_124522 {f : ℝ → ℝ} (hf : ∃ a b c, a ≠ 0 ∧ ∀ x, f x = a * x ^ 2 + b * x + c)
    (h₀ : f (-1) = 0) (h₁ : ∀ x, x ≤ f x ∧ f x ≤ (1 + x ^ 2) / 2) :
    f = fun x => (1 / 4) * x ^ 2 + (1 / 2) * x + (1 / 4) := by
  rcases hf with ⟨a, b, c, ha, hf_eq⟩
  have h1 := (h₁ 1).1
  simp [hf_eq] at h1
  have h2 := (h₁ 1).2
  simp [hf_eq] at h2
  have h3 := (h₁ 0).1
  simp [hf_eq] at h3
  have h4 := (h₁ 0).2
  simp [hf_eq] at h4
  have h5 := (h₁ 2).1
  simp [hf_eq] at h5
  have h6 := (h₁ 2).2
  simp [hf_eq] at h6
  have eq1 : f (-1) = a * (-1) ^ 2 + b * (-1) + c := hf_eq (-1)
  rw [eq1] at h₀
  have eq2 : f 1 = a * 1 ^ 2 + b * 1 + c := hf_eq 1
  have eq3 : f 0 = a * 0 ^ 2 + b * 0 + c := hf_eq 0
  have eq4 : f 2 = a * 2 ^ 2 + b * 2 + c := hf_eq 2
  have h14 : a - b + c = 0 := by linarith
  have h10 : a + b + c = 1 := by linarith
  have hb1 : b = 1 / 2 := by linarith
  have h11 : a + c = 1 / 2 := by linarith
  have h9 : ∀ x : ℝ, a * x ^ 2 + b * x + c ≥ x := by
    intro x
    have h10 := (h₁ x).1
    have eq5 : f x = a * x ^ 2 + b * x + c := hf_eq x
    linarith [eq5, h10]
  have h110 : ∀ x : ℝ, a * x ^ 2 + (b - 1) * x + c ≥ 0 := by
    intro x
    have h1000 := h9 x
    have : a * x ^ 2 + (b - 1) * x + c = a * x ^ 2 + b * x + c - x := by ring
    rw [this] at *
    linarith
  have h131 : a > 0 := by
    by_contra h
    push_neg at h
    have h_eq : a ≤ 0 := by nlinarith
    have h130 : a ≤ 0 := by nlinarith
    have h114 : a * (100 : ℝ) ^ 2 + (b - 1) * (100 : ℝ) + c ≥ 0 := by
      apply h110 100
    nlinarith
  have h155 : a = 1 / 4 := by
    have eq24 : c ≥ 1 / (16 * a) := by
      have h114 : a * ((1 - b) / (2 * a)) ^ 2 + (b - 1) * ((1 - b) / (2 * a)) + c ≥ 0 := by
        apply h110
      have eq13 : a * ((1 - b) / (2 * a)) ^ 2 + (b - 1) * ((1 - b) / (2 * a)) + c = -1 / (16 * a) + c := by
        rw [hb1]
        field_simp
        ring
      rw [eq13] at h114
      have h1311 : a > 0 := h131
      have eq24 : -1 / (16 * a) + c ≥ 0 := by linarith
      have eq25 : c ≥ 1 / (16 * a) := by
        have h1311 : a > 0 := h131
        have eq26 : -1 / (16 * a) + c ≥ 0 := by linarith
        have eq27 : c ≥ 1 / (16 * a) := by
          have h1311 : a > 0 := h131
          have h100 : 16 * a > 0 := by nlinarith
          have h101 : c ≥ 1 / (16 * a) := by
            have h102 : -1 / (16 * a) + c ≥ 0 := eq26
            have h103 : c ≥ 1 / (16 * a) := by
              have h104 : -1 / (16 * a) + c = (c - 1 / (16 * a))
                := by ring
              rw [h104] at h102
              have h105 : c ≥ 1 / (16 * a) := by
                by_contra h
                push_neg at h
                have h110 : c < 1 / (16 * a) := by linarith
                nlinarith
              linarith
            linarith
          linarith
        linarith
      linarith
    have h106 : a + 1 / (16 * a) ≤ 1 / 2 := by
      have h120 : a + 1 / (16 * a) ≤ a + c := by
        have h120 : 1 / (16 * a) ≤ c := by
          have eq244 : c ≥ 1 / (16 * a) := eq24
          linarith
        nlinarith
      have h113 : a + c = 1 / 2 := h11
      linarith
    have h137 : 16 * a ^ 2 - 8 * a + 1 ≤ 0 := by
      have h138 : a + 1 / (16 * a) ≤ 1 / 2 := h106
      have h139 : a > 0 := h131
      have h140 : 16 * a ^ 2 + 1 ≤ 8 * a := by
        have h141 : a + 1 / (16 * a) ≤ 1 / 2 := h138
        have h147 : (a + 1 / (16 * a)) * (16 * a) = 16 * a ^ 2 + 1 := by
          field_simp
          <;> nlinarith
        have h148 : (a + 1 / (16 * a)) * (16 * a) ≤ (1 / 2) * (16 * a) := by
          apply mul_le_mul_of_nonneg_right
          linarith
          nlinarith
        have h149 : (1 / 2) * (16 * a) = 8 * a := by
          linarith
        nlinarith
      nlinarith
    have h142 : (4 * a - 1) ^ 2 ≤ 0 := by
      nlinarith
    have h143 : (4 * a - 1) ^ 2 = 0 := by
      linarith [sq_nonneg (4 * a - 1)]
    have h144 : 4 * a - 1 = 0 := by
      rw [sq_eq_zero_iff] at h143
      linarith
    linarith
  have hc173 : c = 1 / 4 := by
    rw [h155] at h11
    linarith
  funext x
  have eq20 : f x = (1 / 4) * x ^ 2 + (1 / 2) * x + (1 / 4) := by
    rw [hf_eq x]
    rw [h155, hb1, hc173]
    all_goals
      ring
  exact eq20