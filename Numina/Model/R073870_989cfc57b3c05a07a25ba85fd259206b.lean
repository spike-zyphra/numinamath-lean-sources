import Mathlib

theorem algebra_17247 (shirts : Finset ℕ) (h : shirts.card = 3) (pants : Finset ℕ) (hp : pants.card = 4) :
    {x | ∃ i ∈ shirts, ∃ j ∈ pants, x = (i, j)}.ncard = 12 := by
  have h1 : {x | ∃ i ∈ shirts, ∃ j ∈ pants, x = (i, j)} = shirts ×ˢ pants := by
    ext ⟨i, j⟩
    simp [Finset.mem_product]
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  have h2 : (shirts ×ˢ pants).card = 12 := by
    rw [Finset.card_product]
    have h3 : (shirts.card) = 3 := h
    have h4 : (pants.card) = 4 := hp
    calc
      (shirts.card) * (pants.card) = 3 * (pants.card) := by rw [h3]
      _ = 3 * 4 := by rw [hp]
      _ = 12 := by norm_num
  rw [h2]