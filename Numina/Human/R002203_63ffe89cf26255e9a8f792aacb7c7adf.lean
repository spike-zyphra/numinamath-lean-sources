import Mathlib

theorem algebra_72671 :
  IsGreatest {Finset.card S | (S : Finset ℝ) (_ : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (x + y - 1) ^ 2 = x * y + 1)} 3 := by


  have : √5 > 0 := by positivity
  have h_sqrt5: √5^2 = 5 := by rw [Real.sq_sqrt (by norm_num)]

  unfold IsGreatest upperBounds
  simp

  constructor
  . use {1, 1/2 * (1 + √5), 1/2 * (1 - √5)}
    constructor
    . intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | rfl | rfl
      . rcases hy with rfl | rfl | rfl
        . norm_num at hxy
        . ring_nf
          rw [h_sqrt5]
          linarith
        . ring_nf
          rw [h_sqrt5]
          linarith
      . rcases hy with rfl | rfl | rfl
        . ring_nf
          rw [h_sqrt5]
          linarith
        . norm_num at hxy
        . ring_nf
          rw [h_sqrt5]
          linarith
      . rcases hy with rfl | rfl | rfl
        . ring_nf
          rw [h_sqrt5]
          linarith
        . ring_nf
          rw [h_sqrt5]
          linarith
        . norm_num at hxy

    . repeat rw [Finset.card_insert_of_not_mem]
      all_goals simp
      . by_contra h_contra
        linarith
      . constructor
        . by_contra h_contra
          field_simp at h_contra
          have : √5 = 1 := by linarith
          norm_num at this

        . by_contra h_contra
          linarith

  . intro S heq

    have h_add_2 : ∀ a b c, (a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) → a + b + c = 2 := by
      intro a b c ⟨ha, hb, hc, hab, hac, hbc⟩
      have heq_ab := heq a ha b hb hab
      have heq_ac := heq a ha c hc hac

      have : (a + b - 1) ^ 2 - (a + c - 1) ^ 2 - a*b+a*c = 0 := by
        rw [heq_ab, heq_ac]
        linarith

      ring_nf at this

      have : (b-c) * (a+b+c-2) = 0 := by
        rw [← this]
        ring_nf

      simp at this
      rcases this with h1 | h2
      . have : b = c := by linarith
        contradiction
      . linarith

    by_contra h_contra
    simp at h_contra

    have h4 : ∃ a b c d , a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ c ∧ a ≠d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by

      have : 4 ≤ S.card := by linarith
      rw [Finset.le_card_iff_exists_subset_card] at this
      obtain ⟨T, hTS, hTcard⟩ := this
      rw [Finset.card_eq_succ] at hTcard
      obtain ⟨d, T', hT1, hT2, hT3⟩ := hTcard
      rw [Finset.card_eq_three] at hT3
      obtain ⟨a, b, c, h_ab, h_ac, h_bc, h_abc⟩ := hT3
      use a, b, c, d

      rw [← hT2] at hTS
      rw [Finset.insert_subset_iff] at hTS
      obtain ⟨h_d, h_T'⟩ := hTS
      rw [h_abc] at h_T'

      have : a ∈ ({a, b, c}:Finset ℝ) := by
        simp
      have : b ∈ ({a, b, c}:Finset ℝ) := by
        simp
      have : c ∈ ({a, b, c}:Finset ℝ) := by
        simp


      have : d ≠ a := by
        by_contra h_contra
        subst d
        rw [h_abc] at hT1
        simp at hT1
      have : d ≠ b := by
        by_contra h_contra
        subst d
        rw [h_abc] at hT1
        simp at hT1
      have : d ≠ c := by
        by_contra h_contra
        subst d
        rw [h_abc] at hT1
        simp at hT1

      tauto

    rcases h4 with ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩

    have : a+b+c = 2 := h_add_2 a b c ⟨ha, hb, hc, hab, hac, hbc⟩
    have : b+c+d = 2 := h_add_2 b c d ⟨hb, hc, hd, hbc, hbd, hcd⟩

    have : a = d := by linarith
    contradiction
