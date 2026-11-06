import Mathlib

theorem algebra_14566 (high_blood heart_trouble total: Finset ℕ) (htotal : total.card = 120)
    (hsubset : high_blood ⊆ total ∧ heart_trouble ⊆ total)
    (hb : high_blood.card = 70) (ht : heart_trouble.card = 40)
    (hb_and_ht : (high_blood ∩ heart_trouble).card = 20) :
    (total \ (high_blood ∪ heart_trouble)).card / total.card = (0.25 : ℝ) := by
  have h1 : high_blood ∪ heart_trouble ⊆ total := by
    have h2 := hsubset.1
    have h3 := hsubset.2
    rw [Finset.subset_iff]
    intro x hx
    simp at hx ⊢
    tauto
  have h2 : (high_blood ∪ heart_trouble).card = 90 := by
    calc
      (high_blood ∪ heart_trouble).card = high_blood.card + heart_trouble.card - (high_blood ∩ heart_trouble).card := by
        rw [Finset.card_union]
      _ = 70 + 40 - 20 := by
        rw [hb, ht, hb_and_ht]
      _ = 90 := by
        norm_num
  have h3 : (total \ (high_blood ∪ heart_trouble)).card = 30 := by
    have h4 : (high_blood ∪ heart_trouble).card = 90 := h2
    have h5 : (total \ (high_blood ∪ heart_trouble)).card = total.card - (high_blood ∪ heart_trouble).card := by
      rw [Finset.card_sdiff]
      all_goals
      try { 
        have h1' : high_blood ∪ heart_trouble ⊆ total := h1
        tauto 
      }
    rw [h5, htotal, h4]
    all_goals norm_num
  rw [h3, htotal]
  norm_num