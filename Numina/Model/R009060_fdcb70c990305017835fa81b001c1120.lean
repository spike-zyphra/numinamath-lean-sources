import Mathlib.Tactic

open scoped Set

theorem number_theory_122378 :
    ∃ s : Finset ℕ, s.card = 1985 ∧
      (∀ n ∈ s, n > 0) ∧
      (∃ m : ℕ, m^3 = ∑ n ∈ s, n^2) ∧
      (∃ p : ℕ, p^2 = ∑ n ∈ s, n^3) := by
-- we will use the numbers 1 to 1985 for the problem, so first define b as sum of their squares and c as sum of their cubes and a to be the image of applying i => i*b^4*c^3 on the numbers
  let b := ∑ i ∈ Finset.Icc 1 1985, i^2
  let c := ∑ i ∈ Finset.Icc 1 1985, i^3
  let a := Finset.image (fun i => i * b^4 * c^3) (Finset.Icc 1 1985)
  -- first of all , both b and c are positive, as sum of i^n is positive for any i on those numbers
  have h_pos (n : ℕ) : 0 < ∑ i ∈ Finset.Icc 1 1985, i^n := by
    apply Finset.sum_pos
    . rintro i hi
      apply Nat.pos_pow_of_pos
      simp at hi
      linarith
    . simp
  -- also define the positiveness of b^4 and c^3, will be useful
  have hb_pos : 0 < b := h_pos 2
  have hb_pos' := Nat.pos_pow_of_pos 4 hb_pos
  have hc_pos : 0 < c := h_pos 3
  have hc_pos' := Nat.pos_pow_of_pos 3 hc_pos
  -- prove that the function i => i * b^4 * c^3 is injective
  have hinj : Function.Injective (fun i => i * b^4 * c^3) := by
    rintro x y hxy
    simp at hxy
    simp [show c ≠ 0 by linarith, show b ≠ 0 by linarith] at hxy
    exact hxy
  use a
  and_intros
    -- first of all due to injective ness size of a is also 1985
  . rw [Finset.card_image_of_injective _ hinj]
    simp
  . intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    simp at hi ⊢
    all_goals omega
  . use b^3 * c^2
    native_decide
  . use b^6 * c^5
    native_decide