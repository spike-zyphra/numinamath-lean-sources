import Mathlib

theorem number_theory_123989 (s : Finset (ℤ × ℤ)) (h₀ : s.card = 5) :
    ∃ x y : ℤ, ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ x = ((p.1 + q.1) / 2 : ℚ) ∧ y = ((p.2 + q.2) / 2 : ℚ) := by
  let f : ℤ × ℤ → ℤ × ℤ
    | ⟨x, y⟩ => ⟨x % 2, y % 2⟩
  suffices ∃ p ∈ s, ∃ q ∈ s, f p = f q ∧ p ≠ q by
    rcases this with ⟨p, p_in, q, q_in, f_p_eq_f_q, p_ne_q⟩
    use (p.1 + q.1) / 2 , (p.2 + q.2) / 2, p, p_in, q, q_in, p_ne_q
    have : ∀ i, 2 ∣ i → (i / 2 : ℤ) = (i / 2 : ℚ) := by
      intro i i_dvd
      rcases i_dvd with ⟨j, rfl⟩
      simp --norm_num
    simp [f] at f_p_eq_f_q
    rcases f_p_eq_f_q with ⟨x_eq, y_eq⟩
    rw [show (p.1 + q.1 : ℚ) = (p.1 + q.1 : ℤ) by norm_cast]
    rw [show (p.2 + q.2 : ℚ) = (p.2 + q.2 : ℤ) by norm_cast]
    refine ⟨this (p.1 + q.1) ?_, this (p.2 + q.2) ?_⟩
    . mod_cases p.1 % 2
      . omega
      . omega
    . mod_cases p.2 % 2
      . omega
      . omega
  have : (s.image f).card < s.card := by
    have : s.image f ⊆ {0, 1} ×ˢ {0, 1} := by
      rintro ⟨x, y⟩
      simp [f]
      rintro p q _ rfl rfl
      omega
    have := Finset.card_le_card this
    have : ({0, 1} ×ˢ {0, 1} : Finset (ℤ × ℤ)).card = 4 := by
      rfl
    linarith
  -- Pigeonhole principle
  have not_injOn : ¬ Set.InjOn f s := by
    intro injOn
    have : (Finset.image f s).card = s.card := by
      exact Finset.card_image_iff.mpr injOn
    linarith
  --have : /- ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ f p = f q -/ ∃ p ∈ s, ∃ q ∈ s, f p = f q ∧ p ≠ q := by
  unfold Set.InjOn at not_injOn
  norm_cast at not_injOn
  push_neg at not_injOn
  --rcases not_injOn with ⟨p, p_in, q, q_in, p_ne_q, f_p_eq_f_q⟩
  exact not_injOn
