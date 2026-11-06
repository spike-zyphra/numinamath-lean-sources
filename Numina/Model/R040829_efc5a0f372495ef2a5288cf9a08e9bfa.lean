import Mathlib

theorem number_theory_8004 {a b c d : ℤ} (h : a * d - b * c > 1) :
    ¬(a * d - b * c ∣ a) ∨ ¬(a * d - b * c ∣ b) ∨
    ¬(a * d - b * c ∣ c) ∨ ¬(a * d - b * c ∣ d) := by
  by_contra h1
  push_neg at h1
  rcases h1 with ⟨h1, h2, h3, h4⟩
  set K := a * d - b * c with hK 
  have h6 : K > 1 := by
    linarith
  rcases h1 with ⟨k, hk⟩ 
  rcases h2 with ⟨m, hm⟩ 
  rcases h3 with ⟨n, hn⟩ 
  rcases h4 with ⟨p, hp⟩ 
  have eq2 : a * d - b * c = K := by
    linarith [hK]
  rw [show a = K * k by linarith [hk]] at eq2 
  rw [show d = K * p by linarith [hp]] at eq2
  rw [show b = K * m by linarith [hm]] at eq2 
  rw [show c = K * n by linarith [hn]] at eq2
  have h11 : K * k * (K * p) - (K * m) * (K * n) = K := by 
    nlinarith
  have h12 : K * (K * (k * p - m * n)) = K := by 
    ring_nf at h11 ⊢ 
    <;> nlinarith
  have h13 : K ≠ 0 := by 
    nlinarith 
  have h14 : K * (k * p - m * n) = 1 := by 
    apply (mul_left_inj' (show K ≠ 0 by
      exact h13
    )).mp
    linarith
  have h15 : K ∣ 1 := by 
    use (k * p - m * n)
    all_goals 
      linarith [h14]
  have h16 : K = 1 ∨ K = -1 := by 
    have h17 : K ∣ 1 := h15
    have h18 : K ≤ 1 := by 
      apply Int.le_of_dvd (by norm_num) h17 
    have h19 : K ≥ -1 := by 
      have h20 : (-K) ∣ 1 := by 
        exact Int.neg_dvd.2 h17 
      have h21 : -K ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h20 
      omega 
    interval_cases K <;> omega 
  cases h16 with
  | inl h20 => 
    omega 
  | inr h20 => 
    omega