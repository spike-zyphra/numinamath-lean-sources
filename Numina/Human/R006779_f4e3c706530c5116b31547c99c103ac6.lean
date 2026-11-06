import Mathlib

-- lemma : Sum of odd naturals in $S$ modulo $2$ equals card of $S$ modulo $2$.
lemma sum_mod_two (S : Finset ℕ) (h_odds : ∀ m ∈ S, m % 2 = 1) :
    (S.sum id) % 2 = S.card % 2 := by
  have h_odd_members : ∀ x ∈ S, Odd x := fun x hx => Nat.odd_iff.mpr (h_odds x hx)
  -- Show that the set filtered by odd elements is equal to $S$, since all are odd.
  have h_filter_eq : {x ∈ S | Odd (id x)} = S := by
    ext x
    simp only [Finset.mem_filter, Set.mem_sep_iff, and_iff_right_iff_imp, id_eq]
    constructor
    · intro ⟨hx, _⟩
      exact hx
    · intro hx
      exact ⟨hx, h_odd_members x hx⟩
  by_cases h: Odd S.card
  · have h' :Odd (Finset.filter (fun x ↦ Odd (id x)) S).card := by rw [← h_filter_eq] at h; exact h
    have : Odd (S.sum id) := (Finset.odd_sum_iff_odd_card_odd (f := id) ).mpr h'
    have : (S.sum id) % 2 = S.card % 2 := by
      rw [Nat.odd_iff.mp h, Nat.odd_iff.mp this]
    exact this
  · have h' :Even (Finset.filter (fun x ↦ Odd (id x)) S).card := by rw [← h_filter_eq] at h; exact Nat.not_odd_iff_even.mp h
    have : Even (S.sum id) := (Finset.even_sum_iff_even_card_odd (f := id) ).mpr h'
    have : (S.sum id) % 2 = S.card % 2 := by
      rw [Nat.even_iff.mp (Nat.not_odd_iff_even.mp h), Nat.even_iff.mp this]
    exact this

/-Let $N=19$ be the number of positive odd integers. Let $X$ be the sum of these $N$ integers. The average $A = X/N$, when rounded to one decimal place (rounding half up), is $10.5$. Show that the average $A = X/N$, when rounded to two decimal places (rounding half up), is $10.47$.
(For clarity: rounding $V/D$ to $k$ decimal places using integer arithmetic means computing $\lfloor (V \cdot 10^k + D/2) / D \rfloor / 10^k$, where $D/2$ and the final division are integer divisions.)-/
theorem number_theory_641088 (X : ℕ) (h_sum : ∃ S : Finset ℕ, S.card = 19 ∧ (∀ m ∈ S, 1 ≤ m ∧ m % 2 = 1) ∧ X = S.sum id)
    (h_round1 : (10 * X + 9) / 19 = 105) :
    (100 * X + 9) / 19 = 1047 := by
  obtain ⟨S, h_card, h_members, h_X⟩ := h_sum
  have h_odds : ∀ m ∈ S, m % 2 = 1 := fun m hm => (h_members m hm).2
  -- Prove that $X$ is odd using the sum_mod_two lemma and card equals $19$.
  have h_X_odd : X % 2 = 1 := by
    rw [h_X]
    rw [sum_mod_two S h_odds]
    rw [h_card]
  -- -- Conclude $X$ equals $199$ using arithmetic bounds and odd condition.
  have h_X_eq_199 : X = 199 := by omega
  have h_div_eq : (100 * X + 9) / 19 = 1047 := by omega
  exact h_div_eq
