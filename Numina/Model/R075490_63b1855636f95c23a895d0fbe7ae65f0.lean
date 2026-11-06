import Mathlib

theorem number_theory_6898 {a : ℕ} (ha : 1 < a) :
    ∃ p, p.Prime ∧ p ∣ a ∧ p = sInf {d | 1 < d ∧ d ∣ a} := by
  have h1 : {d | 1 < d ∧ d ∣ a}.Nonempty := by
    use a
    constructor
    · linarith
    · exact dvd_refl a
  set p := sInf {d | 1 < d ∧ d ∣ a} with hp_def
  have hp1 : 1 < p := by
    by_contra h
    push_neg at h
    have hp2 : p ∈ {d | 1 < d ∧ d ∣ a}:= by
      apply Nat.sInf_mem h1
    have hp3 : 1 < p := hp2.left
    all_goals linarith
  have hp2 : p ∣ a := by
    have hp2 : p ∈ {d | 1 < d ∧ d ∣ a}:= by
      apply Nat.sInf_mem h1
    exact hp2.right
  have h2 : p.Prime := by
    by_contra h
    push_neg at h
    have hp4 : ∃ d, d ∣ p ∧ 1 < d ∧ d < p := by
      rw [Nat.not_prime_iff_exists_dvd_lt (by omega) ] at h 
      obtain ⟨d, ⟨hd1, hd2⟩⟩ := h 
      use d 
      all_goals omega
    rcases hp4 with ⟨d, ⟨hd1, hd2, hd3⟩⟩
    have hp5 : d ∣ a := by
      exact dvd_trans hd1 hp2
    have hp6 : 1 < d := hd2
    have hp7 : d < p := hd3
    have hd2 : d ∈ {d | 1 < d ∧ d ∣ a} := ⟨hp6, hp5⟩
    have hp8 : p ≤ d := by
      apply Nat.sInf_le
      exact hd2
    all_goals omega
  exact ⟨p, h2, hp2, by simp [hp_def]⟩