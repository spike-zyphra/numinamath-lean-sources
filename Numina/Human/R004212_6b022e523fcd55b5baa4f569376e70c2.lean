import Mathlib

set_option maxHeartbeats 500000


theorem number_theory_242998
  (a b c d e : ℕ)
  (h1 : {a, b, c, d, e} = ({2, 3, 4, 5, 6} : Set ℕ))
  (h2 : IsSquare (Nat.ofDigits 10 [d, c, b]))
  (h3 : IsSquare (Nat.ofDigits 10 [e, c, a])) :
  c = 2 := by
  obtain ⟨m, hm⟩ := h2
  obtain ⟨n, hn⟩ := h3

  have ⟨h_2_le_a, h_a_le_6⟩ : 2 ≤ a ∧ a ≤ 6 := by
    have : a ∈ ({a, b, c, d, e}: Set ℕ) := by simp
    rw [h1] at this
    simp at this
    omega

  have ⟨h_2_le_b, h_b_le_6⟩ : 2 ≤ b ∧ b ≤ 6 := by
    have : b ∈ ({a, b, c, d, e}: Set ℕ) := by simp
    rw [h1] at this
    simp at this
    omega

  have ⟨h_2_le_c, h_c_le_6⟩ : 2 ≤ c ∧ c ≤ 6 := by
    have : c ∈ ({a, b, c, d, e}: Set ℕ) := by simp
    rw [h1] at this
    simp at this
    omega

  have ⟨h_2_le_d, h_d_le_6⟩ : 2 ≤ d ∧ d ≤ 6 := by
    have : d ∈ ({a, b, c, d, e}: Set ℕ) := by simp
    rw [h1] at this
    simp at this
    omega

  have ⟨h_2_le_e, h_e_le_6⟩ : 2 ≤ e ∧ e ≤ 6 := by
    have : e ∈ ({a, b, c, d, e}: Set ℕ) := by simp
    rw [h1] at this
    simp at this
    omega

  have ⟨hm_range, hm_range_2⟩ : 15 ≤ m ∧ m ≤ 25 := by
    have h1 : 222 ≤ m * m := by
      rw [← hm]
      simp [Nat.ofDigits]
      omega

    have h2 : m * m ≤ 666 := by
      rw [← hm]
      simp [Nat.ofDigits]
      omega

    constructor <;> nlinarith

  have ⟨hn_range, hn_range_2⟩ : 15 ≤ n ∧ n ≤ 25 := by
    have h1 : 222 ≤ n * n := by
      rw [← hn]
      simp [Nat.ofDigits]
      omega

    have h2 : n * n ≤ 666 := by
      rw [← hn]
      simp [Nat.ofDigits]
      omega

    constructor <;> nlinarith


  have h_digits_m_m : [d, c, b] = Nat.digits 10 (m * m) := by
    rw [← hm, Nat.digits_ofDigits]
    . norm_num
    . intro l hl
      simp at hl
      rcases hl with rfl | rfl | rfl
      all_goals omega
    . intro h
      simp
      omega

  have h_digits_n_n : [e, c, a] = Nat.digits 10 (n * n) := by
    rw [← hn, Nat.digits_ofDigits]
    . norm_num
    . intro l hl
      simp at hl
      rcases hl with rfl | rfl | rfl
      all_goals omega
    . intro h
      simp
      omega

  interval_cases m
  all_goals interval_cases n
  all_goals try simp at h_digits_m_m
  all_goals try simp at h_digits_n_n
  all_goals try omega
  obtain ⟨h1, h2, h3⟩ := h_digits_m_m
  obtain ⟨h4, h5, h6⟩ := h_digits_n_n

  subst a b c d e
  simp at h1
  have : (3 : ℕ) ∈ ({2, 3, 4, 5, 6} : Set ℕ) := by simp
  rw [← h1] at this
  simp at this
