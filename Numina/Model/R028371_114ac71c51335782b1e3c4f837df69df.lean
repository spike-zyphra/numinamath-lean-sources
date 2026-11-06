import Mathlib


open Complex


lemma lemma_1 {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0)
    (h1 : z + 20 * I / w = 5 + I) (h2 : w + 12 * I / z = -4 + 10 * I)
    (P : ℂ) (hP : P = z * w) :
    P ^ 2 + (30 - 14 * I) * P - 240 = 0 := by
  have eq1 : z * w + 20 * I = (5 + I) * w := by
    have h := h1
    field_simp [hw] at h
    <;> simpa using h
  have eq2 : w * z + 12 * I = (-4 + 10 * I) * z := by
    have h := h2
    field_simp [hz] at h
    <;> simpa using h
  have eq4 : P + 20 * I = (5 + I) * w := by
    calc
      P + 20 * I = z * w + 20 * I := by rw [hP]
      _ = (5 + I) * w := by rw [eq1]
  have eq5 : P + 12 * I = (-4 + 10 * I) * z := by
    calc
      P + 12 * I = w * z + 12 * I := by rw [show w * z = z * w by ring_nf, hP]
      _ = (-4 + 10 * I) * z := by rw [eq2]
  have eq6 : w = (P + 20 * I) / (5 + I) := by
    have hne : 5 + I ≠ 0 := by
      norm_num [Complex.ext_iff]
      <;> norm_num [Real.sqrt_pos.mpr]
    field_simp [hne]
    <;> rw [eq4]
    <;> ring_nf
    <;> norm_num [Complex.ext_iff]
    all_goals tauto
  have eq7 : z = (P + 12 * I) / (-4 + 10 * I) := by
    have hne : -4 + 10 * I ≠ 0 := by
      norm_num [Complex.ext_iff]
      <;> norm_num [Real.sqrt_pos.mpr]
    field_simp [hne]
    <;> rw [eq5]
    <;> ring_nf
    <;> norm_num [Complex.ext_iff]
    all_goals tauto
  have eq9 : P * (-4 + 10 * I) * (5 + I) = (P + 12 * I) * (P + 20 * I) := by
    have eq10 : P = ((P + 20 * I) / (5 + I)) * ((P + 12 * I) / (-4 + 10 * I)) := by
      have eq13 : P = w * z := by
        have eq8'' : P = z * w := hP
        rw [show z * w = w * z by ring_nf] at eq8''
        exact_mod_cast eq8''

      rw [show ((P + 20 * I) / (5 + I)) * ((P + 12 * I) / (-4 + 10 * I)) = w * z by
        rw [show w = (P + 20 * I) / (5 + I) by rw [eq6]]
        rw [show z = (P + 12 * I) / (-4 + 10 * I) by rw [eq7]]
        <;> ring_nf
      ] at *
      <;> rw [eq13]
      all_goals ring_nf
      <;> try tauto
    field_simp [(show (5 + I) ≠ 0 by
      norm_num [Complex.ext_iff]
      <;> norm_num [Real.sqrt_pos.mpr]
    ), (show (-4 + 10 * I) ≠ 0 by
      norm_num [Complex.ext_iff]
      <;> norm_num [Real.sqrt_pos.mpr]
    )] at eq10 ⊢
    <;> ring_nf at eq10 ⊢
    <;> norm_num [Complex.ext_iff] at eq10 ⊢
    all_goals try tauto
    all_goals try nlinarith
  have eq11 : P * (-4 + 10 * I) * (5 + I) = P * (-30 + 46 * I) := by
    ring_nf
    <;> norm_num [Complex.ext_iff]
    all_goals ring_nf <;> norm_num
  have eq12 : (P + 12 * I) * (P + 20 * I) = P ^ 2 + 32 * I * P - 240 := by
    calc
      (P + 12 * I) * (P + 20 * I) = P ^ 2 + (20 * I + 12 * I) * P + (12 * I) * (20 * I) := by ring_nf
      _ = P ^ 2 + (32 * I) * P + (12 * I) * (20 * I) := by
        ring_nf
      _ = P ^ 2 + (32 * I) * P + (240 : ℂ) * (I * I) := by
        ring_nf
      _ = P ^ 2 + (32 * I) * P + (240 : ℂ) * (-1) := by
        rw [I_mul_I]
        <;> norm_num [Complex.ext_iff]
        all_goals tauto
      _ = P ^ 2 + 32 * I * P - 240 := by
        ring_nf
        <;> norm_num [Complex.ext_iff]
        all_goals tauto
  rw [eq11, eq12] at eq9
  have eq13 : P ^ 2 + (30 - 14 * I) * P - 240 = 0 := by
    have eq14 : P ^ 2 + 32 * I * P - 240 - (P * (-30 + 46 * I)) = 0 := by
      calc
        P ^ 2 + 32 * I * P - 240 - (P * (-30 + 46 * I)) = (P ^ 2 + 32 * I * P - 240) - (P * (-30 + 46 * I)) := by ring
        _ = (P * (-30 + 46 * I)) - (P * (-30 + 46 * I)) := by rw [eq9]
        _ = 0 := by ring
    calc
      P ^ 2 + (30 - 14 * I) * P - 240
      = P ^ 2 + 30 * P - 14 * I * P - 240 := by ring_nf
      _ = P ^ 2 + 32 * I * P - 240 - (P * (-30 + 46 * I)) := by
        ring_nf
        <;> simp [Complex.ext_iff, mul_add, add_mul]
        all_goals ring_nf <;> norm_num [Complex.ext_iff]
        all_goals try tauto
      _ = 0 := by rw [eq14]
  exact_mod_cast eq13


theorem algebra_95383 (S : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℝ) (hS : S = { (z ,w) | z * w ≠ 0 ∧ z + 20 * I / w = 5 + I ∧ w + 12 * I / z = -4 + 10 * I})
    (hf : f = fun (z, w) ↦ normSq (z * w)) : IsLeast (f '' S) 40 := by
  have h1 : ∀ x ∈ S, f x ≥ 40 := by
    rw [hS]
    intro x hx
    have h2 := hx.2.1
    have h3 := hx.2.2
    have h4 : x.1 * x.2 ≠ 0 := by simpa using hx.1
    have h5 : x.1 ≠ 0 := by
      by_contra h
      have : x.1 * x.2 = 0 := by
        rw [h]
        norm_num
      contradiction
    have h6 : x.2 ≠ 0 := by
      by_contra h
      have : x.1 * x.2 = 0 := by
        rw [h]
        norm_num
      contradiction
    have eq7 : (x.1 * x.2) ^ 2 + (30 - 14 * I) * (x.1 * x.2) - 240 = 0 := by
      apply lemma_1 h5 h6 h2 h3 (x.1 * x.2) (by simp)
    have h8 : (x.1 * x.2) = (6 + 2 * I) ∨ (x.1 * x.2) = (-36 + 12 * I) := by
      have eq11 : (x.1 * x.2 - (6 + 2 * I)) * (x.1 * x.2 - (-36 + 12 * I)) = 0 := by
        have eq10 : (x.1 * x.2) ^ 2 + (30 - 14 * I) * (x.1 * x.2) - 240 = 0 := eq7
        rw [show (x.1 * x.2 - (6 + 2 * I)) * (x.1 * x.2 - (-36 + 12 * I))
            = (x.1 * x.2) ^ 2 + (30 - 14 * I) * (x.1 * x.2) - 240 by
          simp [pow_two, Complex.ext_iff]
          <;> ring_nf <;> norm_num [Complex.I_mul_I]
          all_goals try tauto
          ]
        rw [eq10]
        all_goals norm_num [Complex.ext_iff, pow_two]
        all_goals tauto
      cases' (mul_eq_zero.mp eq11) with h10 h11
      · left
        have h14 : x.1 * x.2 - (6 + 2 * I) = 0 := by
          simpa using h10
        have h15 : x.1 * x.2 = 6 + 2 * I := by
          calc
            x.1 * x.2 = x.1 * x.2 - (6 + 2 * I) + (6 + 2 * I) := by ring
            _ = 0 + (6 + 2 * I) := by rw [h14]; all_goals ring_nf <;> norm_num [Complex.ext_iff] <;> tauto
            _ = 6 + 2 * I := by ring_nf
        exact_mod_cast h15
      · right
        have h14 : x.1 * x.2 - (-36 + 12 * I) = 0 := by
          simpa using h11
        have h15 : x.1 * x.2 = -36 + 12 * I := by
          calc
            x.1 * x.2 = x.1 * x.2 - (-36 + 12 * I) + (-36 + 12 * I) := by ring
            _ = 0 + (-36 + 12 * I) := by rw [h14]; all_goals ring_nf <;> norm_num [Complex.ext_iff] <;> tauto
            _ = -36 + 12 * I := by ring_nf
        exact_mod_cast h15
    have eq8 : f x = normSq (x.1 * x.2) := by simp [hf]
    rw [eq8]
    rcases h8 with (h8 | h8)
    · -- The first solution
      rw [h8]
      norm_num [Complex.normSq, pow_two]
      <;> norm_num
    · -- The second solution
      rw [h8]
      norm_num [Complex.normSq, pow_two]
      <;> norm_num
  have h2 : 40 ∈ f '' S := by
    use (1 - I, 2 + 4 * I)
    constructor
    · -- Verify that (z, w) is in S
      rw [hS]
      constructor
      · -- Verify that z * w ≠ 0
        norm_num [Complex.ext_iff, pow_two]
        <;> norm_num
      constructor
      · -- Verify the first equation
        field_simp [Complex.ext_iff, pow_two]
        all_goals norm_num
      · -- Verify the second equation
        field_simp [Complex.ext_iff, pow_two]
        all_goals norm_num
    · -- Compute f(z, w)
      rw [hf]
      simp [Complex.normSq, pow_two]
      <;> norm_num [Complex.ext_iff, pow_two]
      <;> norm_num
  have h3 : ∀ y ∈ f '' S, 40 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h5 := h1 x hx
    linarith
  exact ⟨h2, h3⟩