import Mathlib


/- We draw 51 numbers between 1 and 100.
Show that we can find two such that one of them divides the other. -/
theorem number_theory_127982 (s : Finset ℕ) (h₀ : s.card = 51)
  (h₁ : ∀ n ∈ s, n ∈ Finset.Icc 1 100) :
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a ∣ b := by

  -- we can define odd part of a number.
  have h1: ∀n∈ Finset.Icc 1 100,
    ∃ k m, Odd m ∧ n = 2^k * m := by
    intro n
    simp only [Finset.mem_Icc, and_imp]
    intro hn _
    apply Nat.exists_eq_two_pow_mul_odd (by omega)
  choose! k m h1 using h1

  -- there are 50 odd numbers from 1 to 100.
  set t: Finset ℕ := (Finset.filter (Odd ·) (Finset.Icc 1 100)) with t_def
  have h2: t.card = 50 := by
    rw [t_def]
    decide

  -- for any number in 1 to 100, its odd part fall in set t.
  have h3: ∀n ∈ s, m n ∈ t := by
    intro n hn
    replace hn := h₁ n hn
    specialize h1 n hn
    simp only [t_def, Finset.mem_filter, Finset.mem_Icc,
    h1.left, and_true]
    constructor
    · have: m n ≠ 0 := by
        rintro heq
        simp [heq] at h1
      exact Nat.one_le_iff_ne_zero.mpr this
    · have h3: 2^(k n) ≥ 1 := Nat.one_le_two_pow
      have h4: n ≤ 100 := by
        simp only [Finset.mem_Icc] at hn
        exact hn.right
      apply le_trans ?_ h4
      nth_rw 2 [h1.right]
      exact Nat.le_mul_of_pos_left (m n) h3

  -- then there are two numbers have same odd part.
  have: t.card < s.card := by
    norm_num [h2, h₀]
  replace := Finset.exists_ne_map_eq_of_card_lt_of_maps_to this h3
  rcases this with ⟨a, ha, b, hb, aneb, hab⟩

  -- then a ∣ b or b ∣ a. depends on which is greater.
  by_cases h4: k a ≤ k b
  · use a
    refine ⟨ha, b, hb, ⟨aneb, ?_⟩ ⟩
    rw [(h1 a (h₁ a ha)).right,
    (h1 b (h₁ b hb)).right, hab]
    refine Nat.mul_dvd_mul_right ?_ (m b)
    exact Nat.pow_dvd_pow_iff_le_right'.mpr h4
  · push_neg at h4
    use b
    refine ⟨hb, a, ha, ⟨aneb.symm, ?_⟩ ⟩
    rw [(h1 a (h₁ a ha)).right,
    (h1 b (h₁ b hb)).right, hab]
    refine Nat.mul_dvd_mul_right ?_ _
    apply Nat.pow_dvd_pow_iff_le_right'.mpr h4.le