import Mathlib

/-John needs to pay 2010 dollars for his dinner. He has an unlimited supply of 2, 5, and 10 dollar notes.
In how many ways can he pay?-/

theorem combinatorics_608647:
  {(x, y, z): ℕ × ℕ × ℕ | 2 * x + 5 * y + 10 * z = 2010}.encard = 20503 := by

  set t:= {(x, y, z): ℕ × ℕ × ℕ | 2 * x + 5 * y + 10 * z = 2010}
  set s:= (Finset.range 202 ×ˢ Finset.range 202 ×ˢ Finset.range 202).filter (fun (x, y, z) => x + y + z = 201)

  -- we first count the card of s
  have hs: s.card = 20503 := by
    simp [s]
    native_decide
  set s':= (s: Set (ℕ × ℕ × ℕ))
  replace hs: s'.encard = 20503 := by
    simp [s']
    simp [hs]
  rw [← hs]
  clear hs

  -- then we construct bijection between s and t to compute the card
  let f: ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun (x, y, z) =>  (5 * x, 2 * y, z)
  have hf:  Function.Injective f := by
    intro ⟨x, y, z⟩ ⟨a, b, c⟩ h
    simp [f] at h
    simp [h]
  have h: (f '' s').encard = s'.encard := by
    apply Function.Injective.encard_image hf
  rw [← h]
  suffices f '' s' = t by
    rw [this]
  clear h
  ext ⟨x, y, z⟩
  constructor

  -- the forward direction
  .
    intro h
    simp [s', s] at h
    simp [t]
    obtain ⟨a, b, c, h⟩ := h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨h1, h3⟩
    simp [f] at h2
    rcases h2 with ⟨g1, g2, g3⟩
    simp [← g1, ← g2, ← g3]
    clear *- h3
    omega

  -- the backward direction
  .
    intro h
    simp [t] at h
    simp [s', s]
    have uy: 2 ∣ y := by
      suffices 2 ∣ 5 * y by
        apply Nat.Coprime.dvd_of_dvd_mul_left at this
        tauto
        norm_num
      rw [show 5 * y = 2 * x + 5 * y + 10 * z - 2 * (x + 5 * z) by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        rw [h]
        norm_num
      .
        simp
    have ux: 5 ∣ x := by
      suffices 5 ∣ 2 * x by
        apply Nat.Coprime.dvd_of_dvd_mul_left at this
        tauto
        norm_num
      rw [show 2 * x = 2 * x + 5 * y + 10 * z - 5 * (y + 2 * z) by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        rw [h]
        norm_num
      .
        simp
    apply exists_eq_mul_right_of_dvd at uy
    obtain ⟨b, uy⟩ := uy
    apply exists_eq_mul_right_of_dvd at ux
    obtain ⟨a, ux⟩ := ux
    use a, b, z
    refine ⟨?_, ?_⟩
    .
      omega
    .
      simp [f]
      omega