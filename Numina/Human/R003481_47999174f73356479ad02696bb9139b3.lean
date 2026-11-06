import Mathlib

-- Prozvolov V.V.

-- Given fifty different natural numbers, twenty-five of which do not exceed 50, and the rest are greater than 50 but do not exceed 100. Moreover, no two of them differ exactly by 50. Find the sum of these numbers.

-- Вычтем 50 из каждого числа, которое больше 50. Получатся 50 разных чисел, то есть числа от 1 до 50 . Их сумма равна $1+2+\ldots+50=25 \cdot 51$, а сумма исходных чисел $-25 \cdot 51+25 \cdot 50=25 \cdot 101$.

-- ## Oтвет

-- 2525.

theorem number_theory_186951
  (A B : Finset ℕ)
  (hA_card : A.card = 25)
  (hB_card : B.card = 25)
  (hA_range : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 50)
  (hB_range : ∀ b ∈ B, 51 ≤ b ∧ b ≤ 100)
  (hAB_diff : ∀ a ∈ A, ∀ b ∈ B, b - a ≠ 50) :
    A.sum id + B.sum id = 2525 := by

  have h_A_B_disjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx_A hx_B
    have hx_A_range := hA_range x hx_A
    have hx_B_range := hB_range x hx_B
    omega

  let A_add_50 := A.image (fun a => a + 50)

  have h_A_add_50_disjoint : Disjoint A_add_50 B := by
    rw [Finset.disjoint_left]
    intro x hx_A_add_50 hx_B
    unfold A_add_50 at hx_A_add_50
    simp at hx_A_add_50
    obtain ⟨a, ha_mem, ha_eq⟩ := hx_A_add_50
    rw [←ha_eq] at hx_B
    have := hAB_diff a ha_mem (a + 50) hx_B
    norm_num at this

  have h_A_add_50_card: A_add_50.card = A.card := by
    rw [Finset.card_image_of_injective]
    intro x y hx_eq
    simp at hx_eq
    omega  -- x + 50 = y + 50 implies x = y

  have h_A_add_50_B_card: (A_add_50 ∪ B).card = 50 := by
    rw [Finset.card_union_of_disjoint h_A_add_50_disjoint]
    rw [h_A_add_50_card, hA_card, hB_card]

  have h_A_add_50_B_union : A_add_50 ∪ B = Finset.Icc 51 100 := by
    have : A_add_50 ∪ B ⊆ Finset.Icc 51 100 := by
      intro x hx
      simp at hx
      rcases hx with hx_A_add_50 | hx_B
      · unfold A_add_50 at hx_A_add_50
        simp at hx_A_add_50
        obtain ⟨a, ha_mem, ha_eq⟩ := hx_A_add_50
        rw [←ha_eq]
        have ha_range := hA_range a ha_mem
        simp [Finset.mem_Icc]
        omega  -- 1 ≤ a ≤ 50 implies 51 ≤ a + 50 ≤ 100
      · -- x ∈ B
        have := hB_range x hx_B
        simp [Finset.mem_Icc]
        exact this

    have := Finset.eq_iff_card_le_of_subset this
    rw [h_A_add_50_B_card] at this
    rw [show (Finset.Icc 51 100).card = 50 by decide] at this
    simp at this
    exact this

  have h_A_add_50_B_sum : A_add_50.sum id + B.sum id = 3775 := by
    rw [← Finset.sum_union h_A_add_50_disjoint]
    rw [h_A_add_50_B_union]
    -- ∑{51..100} = ∑{1..100} - ∑{1..50} = 5050 - 1275 = 3775
    decide

  have h_A_sum: A_add_50.sum id = A.sum id + A.card * 50 := by
    unfold A_add_50
    simp
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const, nsmul_eq_mul]
    norm_cast

  have h_A_B_sum : A.sum id + B.sum id = 2525 := by
    have : A.sum id + A.card * 50 + B.sum id = 3775 := by
      rw [← h_A_sum]
      exact h_A_add_50_B_sum
    rw [hA_card] at this
    -- A.sum + 1250 + B.sum = 3775
    -- A.sum + B.sum = 2525
    omega

  exact h_A_B_sum
