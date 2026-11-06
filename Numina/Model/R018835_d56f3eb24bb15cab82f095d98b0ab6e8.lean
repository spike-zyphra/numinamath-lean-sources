import Mathlib


open Int


lemma lemma_1 {A B K : ℤ} (hK : Odd K) (hAB : A^2 + B^2 = K^2) :
    Odd A ∧ Even B ∨ Even A ∧ Odd B := by
  by_contra h
  push_neg at h
  have h1 : ¬ (Odd A ∧ Even B) := by
    tauto
  have h2 : ¬ (Even A ∧ Odd B) := by
    tauto
  have h4 : (Odd A → Odd B) := by
    intro hA1
    by_contra h
    push_neg at h
    have hB : Even B := by
      simpa using h
    have hA' : Odd A := hA1
    have h5 : Odd A ∧ Even B := ⟨hA', hB⟩
    have h6 : ¬ (Odd A ∧ Even B) := h1
    tauto
  have h5 : (Even A → Even B) := by
    intro hA1
    by_contra h
    push_neg at h
    have hB : Odd B := by
      simpa using h
    have hA' : Even A := hA1
    have h6 : Even A ∧ Odd B := ⟨hA', hB⟩
    have h7 : ¬ (Even A ∧ Odd B) := h2
    tauto
  by_cases hA : Odd A
  ·
    have hB : Odd B := h4 hA
    have hK1 : K % 8 = 1 ∨ K % 8 = 3 ∨ K % 8 = 5 ∨ K % 8 = 7 := by
      obtain ⟨k, hk⟩ := hK
      omega
    have hA1 : A % 8 = 1 ∨ A % 8 = 3 ∨ A % 8 = 5 ∨ A % 8 = 7 := by
      obtain ⟨m, hm⟩ := hA
      omega
    have hB1 : B % 8 = 1 ∨ B % 8 = 3 ∨ B % 8 = 5 ∨ B % 8 = 7 := by
      obtain ⟨m, hm⟩ := hB
      omega
    have hAsq : A ^ 2 % 8 = 1 := by
      rcases hA1 with (hA1 | hA1 | hA1 | hA1) <;> norm_num [hA1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have hBsq : B ^ 2 % 8 = 1 := by
      rcases hB1 with (hB1 | hB1 | hB1 | hB1) <;> norm_num [hB1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have hABsq : (A^2 + B^2) % 8 = 2 := by
      omega
    have hKsq : K ^ 2 % 8 = 1 := by
      rcases hK1 with (hK1 | hK1 | hK1 | hK1) <;> norm_num [hK1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h7 : (A ^ 2 + B ^ 2) % 8 = K ^ 2 % 8 := by
      omega
    rw [hABsq] at h7
    rw [hKsq] at h7
    all_goals omega
  ·
    have hA' : Even A := by
      simpa using hA
    have hB' : Even B := h5 hA'
    have hK1 : K % 4 = 1 ∨ K % 4 = 3 := by
      obtain ⟨k, hk⟩ := hK
      omega
    have hA1 : A % 2 = 0 := by
      obtain ⟨k, hk⟩ := hA'
      omega
    have hB1 : B % 2 = 0 := by
      obtain ⟨k, hk⟩ := hB'
      omega
    have hA2 : A % 4 = 0 ∨ A % 4 = 2 := by
      omega
    have hB2 : B % 4 = 0 ∨ B % 4 = 2 := by
      omega
    have h1 : A ^ 2 % 4 = 0 := by
      rcases hA2 with (hA2 | hA2) <;> norm_num [hA2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h2 : B ^ 2 % 4 = 0 := by
      rcases hB2 with (hB2 | hB2) <;> norm_num [hB2, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h7 : (A ^ 2 + B ^ 2) % 4 = 0 := by
      omega
    have h8 : K ^ 2 % 4 = 1 := by
      rcases hK1 with (hK1 | hK1) <;> norm_num [hK1, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h9 : (A ^ 2 + B ^ 2) % 4 = K ^ 2 % 4 := by
      omega
    rw [h7] at h9
    rw [h8] at h9
    all_goals omega


theorem number_theory_221521 (p n : ℕ) (hp : Odd p ∧ Nat.Prime p)
    (hn : 0 < n) (m : Finset (ℤ × ℤ)) (hm : m.card = 8)
    (h : ∃ x y, ∀ x' y' : ℤ, (x', y') ∈ m →
      (x'^2 + y'^2 - x^2 - y^2) % (p ^ n) = 0) :
    ∃ x1 x2 x3 y1 y2 y3 : ℤ, (x1, y1) ∈ m ∧ (x2, y2) ∈ m ∧ (x3, y3) ∈ m ∧
      (x2 - x1) ^ 2 + (y2 - y1) ^ 2 ≡ 0 [ZMOD p ^ (n + 1)] := by
  have h1 : m.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h2
    have h3 : m.card = 0 := by
      simp [h2]
    rw [h3] at hm
    all_goals omega

  rcases h1 with ⟨p1, hp1⟩
  rcases h with ⟨x, y, hxy⟩
  use p1.1, p1.1, p1.1, p1.2, p1.2, p1.2
  have hp11 : (p1.1, p1.2) ∈ m := hp1
  simp [Int.ModEq, pow_two, sub_self, add_zero]
  all_goals
    tauto