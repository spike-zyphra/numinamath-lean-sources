import Mathlib

theorem number_theory_305127 (a d : ℤ) (h : a = 13) (h' : d ≠ 0)
    (h'' : ∃ n, a + d * n = 25) (h''' : ∃ m, a + d * m = 41) :
    2013 ∈ {x | ∃ k, x = a + d * k} := by
  rcases h'' with ⟨n, hn⟩
  rcases h''' with ⟨m, hm⟩
  rw [h] at hn hm
  have h3 : d ∣ 12 := by
    use n
    linarith 
  have h4 : d ∣ 28 := by 
    use m 
    linarith
  have h5 : d ∣ 4 := by
    exact Int.dvd_gcd h3 h4
  have h6 : d ∣ 2000 := by
    have h7 : d ∣ 4 := h5 
    have h8 : (4 : ℤ) ∣ (2000 : ℤ) := by norm_num
    exact dvd_trans h7 h8
  have h7 : (2013 : ℤ) ∈ {x | ∃ k, x = a + d * k} := by
    use (2000 / d)
    have h8 : a = 13 := h
    rw [h8]
    have h9 : d * (2000 / d) = 2000 := by
      have h10 : d ∣ 2000 := h6 
      obtain ⟨c, hc⟩ := h10
      have h11 : 2000 / d = c := by
        rw [hc]
        field_simp [h']
        <;> omega
      rw [h11]
      linarith
    linarith [h9]
  exact h7