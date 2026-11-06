import Mathlib
theorem number_theory_611486 : {n : ℕ | n > 1 ∧ ∃ k : ℕ, ((↑n : ℝ) ^ 2 + 7 * n + 136) / (n - 1) = k ^ 2} = {5, 37}:= by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward direction: if n ∈ {n ∈ ℕ | n > 1 ∧ ∃ k : ℕ, ((↑n : ℝ) ^ 2 + 7 * n + 136) / (n - 1) = k ^ 2}, then n ∈ {5, 37}
    intro h
    rcases h with ⟨h1, h2⟩
    rcases h2 with ⟨k, hk⟩
    -- Rearranging the equation to get (n-1)*k² = n²+7n+136
    replace hk : (n - 1) * k ^ 2 = n ^ 2 + 7 * n + 136:= by
      rify
      field_simp
      rify at h1
      replace h1 : (↑n : ℝ) - 1 > 0:= by linarith
      field_simp at hk
      linarith
    -- Proving that (n-1) divides 144
    have h2 : n - 1 ∣ 144:= by
      set m:= n - 1 with hm
      clear_value m
      replace hm : n = m + 1:= by omega
      subst n
      ring_nf at hk
      replace hk2 : m ∣ 144 + m * 9 + m ^ 2:= by rw [←hk] ; simp
      have g1 : m ∣ m ^ 2:= by exact Dvd.intro_left (m.pow 1) rfl
      have g2 : m ∣ m * 9:= by simp
      replace hk2 : m ∣ 144 + m * 9:= by exact (Nat.dvd_add_iff_left g1).mpr hk2
      replace hk2 : m ∣ 144:= by exact (Nat.dvd_add_iff_left g2).mpr hk2
      exact hk2
    -- Setting m = n-1 to simplify calculations
    have h3 : n ≤ 145 := by
      have h4 : n - 1 ≤ 144 := by 
        exact Nat.le_of_dvd (by omega) h2
      omega
    interval_cases n <;> norm_num at hk <;> try { 
      have h4 : k ≤ 30 := by nlinarith 
      interval_cases k <;> norm_num at hk 
      <;> tauto
    }
  · -- Reverse direction: if n ∈ {5, 37}, then n ∈ {n ∈ ℕ | n > 1 ∧ ∃ k : ℕ, ((↑n : ℝ) ^ 2 + 7 * n + 136) / (n - 1) = k ^ 2}
    rintro (rfl | rfl)
    · constructor
      · norm_num
      · use 7
        norm_num
    · constructor
      · norm_num
      · use 7
        norm_num